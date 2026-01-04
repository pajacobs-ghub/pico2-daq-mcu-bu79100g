// pico2_daq_bu79100g.c
//
// RP2350 Pico2 board as the DAQ-MCU, getting data from 8 BU79100G ADC chips.
//
// PJ 2025-04-06: simple interpreter without any pio interaction
//    2025-04-09: data being collected from MCP3301 chip 0 via SPI0.
//    2025-04-13: have the PIO working to collect MCP3301 0 data.
//    2025-04-14: move PIO-RX pin so that we have room for 8 RX pins.
//    2025-04-15: implement code for reading 8 MCP3301 chips.
//    2025-07-07: Adapt to reading the BU79100G ADC chips.
//    2025-10-04: Adapt to the manufactured-PCB pin assignments.
//    2025-11-14: Delegate internal-trigger duties to the PIC18 COMMS-MCU.
//    2025-11-15: Add commands to enable reporting of a full recording.
//    2025-11-16: 1MSps achieved.
//    2025-12-24: Start with CLK high when getting bits from the BU79100G
//    2026-01-02: Service the Real-time Data Port (RTDP) with the second core.
//                Implemented using hints from the C/C++ SDK manual,
//                the RP2350 datasheet, and code from the examples at
//                https://github.com/raspberrypi/pico-examples/
//
#include "pico/stdlib.h"
#include "pico/multicore.h"
#include "pico/util/queue.h"
#include "hardware/clocks.h"
#include "hardware/gpio.h"
#include "hardware/pio.h"
#include "hardware/uart.h"
#include "hardware/timer.h"
#include "hardware/spi.h"
#include "hardware/dma.h"
#include "pico/binary_info.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <ctype.h>
#include "bu79100g.pio.h"

#define VERSION_STR "v0.22 Pico2 as DAQ-MCU 2026-01-04"
const uint n_adc_chips = 8;

// Names for the IO pins.
// A. For interaction with the PIC18F26Q71 COMMS-MCU.
// UART0_TX on GP0 (default)
// UART0_RX in GP1 (default)
const uint SYSTEM_EVENTn_PIN = 2;
const uint Pico2_EVENT_PIN = 3;
const uint READY_PIN = 15;
// B. For interaction with the BU79100G ADC chips.
const uint PIO_CSn_PIN = 5;
const uint PIO_CLK_PIN = 6;
const uint PIO_RX0_PIN = 7;
const uint PIO_RX1_PIN = 8;
const uint PIO_RX2_PIN = 9;
const uint PIO_RX3_PIN = 10;
const uint PIO_RX4_PIN = 11;
const uint PIO_RX5_PIN = 12;
const uint PIO_RX6_PIN = 13;
const uint PIO_RX7_PIN = 14;
// C. For implementing the Real-Time Data Port.
const uint SPI0_CSn_PIN = 17;
const uint SPI0_SCK_PIN = 18;
const uint SPI0_TX_PIN = 19;
const uint RTDP_DE_PIN = 20;
const uint RTDP_REn_PIN = 21;
const uint DATA_RDY_PIN = 27;
// D. For timing via a logic probe.
const uint TIMING_FLAG_PIN = 26;

static inline void assert_ready()
{
    gpio_put(READY_PIN, 1);
}

static inline void assert_not_ready()
{
    gpio_put(READY_PIN, 0);
}

static inline uint8_t read_system_eventn_line()
{
	return (uint8_t) gpio_get(SYSTEM_EVENTn_PIN);
}

static inline void assert_eventn()
{
	gpio_put(SYSTEM_EVENTn_PIN, 0);
	gpio_set_dir(SYSTEM_EVENTn_PIN, GPIO_OUT);
}

static inline void release_eventn_line()
{
	gpio_set_dir(SYSTEM_EVENTn_PIN, GPIO_IN);
	gpio_pull_up(SYSTEM_EVENTn_PIN);
}

static inline void raise_flag_pin()
{
	gpio_put(TIMING_FLAG_PIN, 1);
}

static inline void lower_flag_pin()
{
	gpio_put(TIMING_FLAG_PIN, 0);
}

const uint LED_PIN = PICO_DEFAULT_LED_PIN;
uint8_t override_led = 0;

static inline void sampling_LED_ON()
{
    gpio_put(LED_PIN, 1);
}

static inline void sampling_LED_OFF()
{
    gpio_put(LED_PIN, 0);
}

static inline void assert_data_ready()
{
    gpio_put(DATA_RDY_PIN, 1);
}

static inline void clear_data_ready()
{
    gpio_put(DATA_RDY_PIN, 0);
}

static inline void enable_RTDP_transceiver()
{
    gpio_put(RTDP_REn_PIN, 0);
    gpio_put(RTDP_DE_PIN, 1);
}

static inline void disable_RTDP_transceiver()
{
    gpio_put(RTDP_REn_PIN, 1);
    gpio_put(RTDP_DE_PIN, 0);
}

// Unlike the AVR DAQ firmware, we are going to hard-code the number of
// channels at 8 (because that is how we have to set up the PIO) and we
// are going to use uint16_t (a.k.a. half-words) as the sample type.
// Sample sets are going to be captured as sets of four uint32_t words,
// that may be decoded into 8 uint16_t half-words.
uint pio_offset_for_8_read_program = 0;

// A place for the current samples.
#define N_CHAN 8
uint16_t res[N_CHAN];

// A place to collect the sample sets as they come in from the ADC chips.
#define N_FULLWORDS 0x00010000
#define MAX_N_SAMPLES (N_FULLWORDS/4)
uint32_t data[N_FULLWORDS];
uint32_t next_fullword_index_in_data;
uint8_t fullword_index_has_wrapped_around;

uint8_t event_n;
uint8_t did_not_keep_up_during_sampling;

// Parameters controlling the device are stored in virtual config registers.
#define NUMREG 5
int vregister[NUMREG]; // working copy in SRAM

void set_registers_to_original_values()
{
    vregister[0] = 10;              // sample period in microseconds (timer ticks)
    // For values between 1 and 20, the timer is user to pace conversions.
    // For a value of 1, the processor tuns flat out and the PIO regulates
    // the pace of conversion.
    vregister[1] = N_CHAN;          // number of channels to sample ia always 8.
    vregister[2] = MAX_N_SAMPLES/2; // number of samples in record after trigger event
    vregister[3] = 0;               // trigger mode 0=immediate, 1=wait for EVENTn
    vregister[4] = 0;               // advertising period (in microseconds) for the RTDP
    // A value of zero will disable the RTDP.
}

static inline uint32_t oldest_fullword_index_in_data()
{
    return (fullword_index_has_wrapped_around) ? next_fullword_index_in_data : 0;
}

static inline void unpack_nybbles_from_word(uint32_t word, uint16_t values[], uint bit_base) {
	//
	// There are 8 by 4-bit values interleaved.
	// 31     24       16       8        0  bits in word
	// |      |        |        |        |
	// 76543210 76543210 76543210 76543210  RX index (rxi)
	// ....bit3 ....bit2 ....bit1 ....bit0  bit in nybble (bin)
	//
	// We assume that the values were initially set to zero.
	// This function, over subsequent calls, sets the bits that are 1.
	for (uint rxi=0; rxi < 8; rxi++) {
		for (uint bin=0; bin < 4; bin++) {
			if (word & (1u << (bin*8 + rxi))) {
				values[rxi] |= 1u << (bin + bit_base);
			}
		}
	}
}

void __no_inline_not_in_flash_func(unpack_sample_set)(uint32_t* here, uint16_t values[]) {
    // Unpacks the four 32-bit words, starting from here.
    unpack_nybbles_from_word(*here, values, 12);
    unpack_nybbles_from_word(*(here+1), values, 8);
    unpack_nybbles_from_word(*(here+2), values, 4);
    unpack_nybbles_from_word(*(here+3), values, 0);
}

//
// core1 services the Real-Time Data Port
// which makes a snapshot of the sampled data available
// to an external SPI master device.
//
// The main loop of the RTDP service function acts upon commands
// sent from core0 via the queue.
//
queue_t RTDP_command_fifo;
#define RTDP_FIFO_LENGTH 1
// The commands themselves are uint values.
#define RTDP_NOP 0
#define RTDP_STOP 99
#define RTDP_ADVERTISE_NEW_DATA 1
// [FIX-ME] Maybe we should use an atomic variable to indicate the status.
static uint RTDP_status;
// The status values are also uint values.
#define RTDP_IDLE 0
#define RTDP_BUSY 1
// core0 will drop a copy of new sample data here.
static uint32_t RTDP_data_words[N_CHAN/2];

void __no_inline_not_in_flash_func(core1_service_RTDP)(void)
{
    uint8_t tx_buffer[N_CHAN*2]; // Send out the data from this buffer.
    // The data sheet seems to indicate that we have to collect
    // the incoming data, even if we don't want it.
    uint8_t rx_buffer[N_CHAN*2]; // Dump the unwanted data here.
    //
    // Transfer bytes to and from the SPI peripheral via DMA channels.
    const uint dma_spi0_tx = dma_claim_unused_channel(true);
    const uint dma_spi0_rx = dma_claim_unused_channel(true);
    dma_channel_config tx_cfg = dma_channel_get_default_config(dma_spi0_tx);
    dma_channel_config rx_cfg = dma_channel_get_default_config(dma_spi0_rx);
    channel_config_set_transfer_data_size(&tx_cfg, DMA_SIZE_8);
    channel_config_set_read_increment(&tx_cfg, true);
    channel_config_set_write_increment(&tx_cfg, false);
    channel_config_set_transfer_data_size(&rx_cfg, DMA_SIZE_8);
    channel_config_set_read_increment(&rx_cfg, false);
    channel_config_set_write_increment(&rx_cfg, true);
    // The dma-transfer requests are paced by the SPI peripheral.
    channel_config_set_dreq(&tx_cfg, spi_get_dreq(spi0, true));
    channel_config_set_dreq(&rx_cfg, spi_get_dreq(spi0, false));
    //
    uint timeout_period_us = vregister[4];
    // At 2MHz, 16 bytes transfer in about 64us,
    // so it does not make much sense to have a very short timeout.
    if (timeout_period_us < 100) timeout_period_us = 100;
    //
    // The main responsibility of core1 is to look for incoming commands and act.
    // This provides a synchronization mechanism, such that core1 advertises
    // available data only when core0 has put some new data into RTP_data_words,
    // and core0 will only put new data in that array while core1 is active and idle.
    //
    RTDP_status = RTDP_IDLE;
    bool my_spi_is_initialized = false;
    bool active = true;
    while (active) {
        // Wait until we are commanded to do something.
        uint cmd = RTDP_NOP;
        queue_remove_blocking(&RTDP_command_fifo, &cmd);
        switch (cmd) {
        case RTDP_ADVERTISE_NEW_DATA:
            { // start new scope
                RTDP_status = RTDP_BUSY;
                #define DEBUG_RTDP 1
                #if DEBUG_RTDP == 1
                // Use faked-but-known values.
                uint16_t values[N_CHAN] = {1, 2, 3, 4, 5, 6, 7, 8};
                #else
                // Use the real, sampled data.
                uint16_t values[N_CHAN] = {0, 0, 0, 0, 0, 0, 0, 0};
                unpack_sample_set(RTDP_data_words, values);
                #endif
                for (uint i=0; i < N_CHAN; i++) {
                    // Put the data into the outgoing byte buffer in big-endian layout.
                    tx_buffer[2*i] = (uint8_t) (values[i] & 0xff00) >> 8;
                    tx_buffer[2*i+1] = (uint8_t) (values[i] & 0x00ff);
                }
                if (!my_spi_is_initialized) {
                    // We (conditionally) do the SPI module initialization here
                    // because it may have been deinitialized by a timeout event,
                    // or this may be the first use.
                    // My reading of Section 12.3.4.4. Clock ratios in the data sheet
                    // seems to indicate that we are limited to about 2MHz serial clock
                    // in slave mode.
                    // If we don't care about the MOSI data, we might go faster.
                    spi_init(spi0, 2000*1000);
                    spi_set_slave(spi0, true);
                    spi_set_format(spi0, 8, SPI_CPOL_0, SPI_CPHA_0, SPI_MSB_FIRST);
                    my_spi_is_initialized = true;
                }
                dma_channel_configure(dma_spi0_tx, &tx_cfg,
                                      &spi_get_hw(spi0)->dr, // write address
                                      tx_buffer, // read address
                                      dma_encode_transfer_count(N_CHAN*2),
                                      true); // can start now...
                dma_channel_configure(dma_spi0_rx, &rx_cfg,
                                      rx_buffer, // write address
                                      &spi_get_hw(spi0)->dr, // read address
                                      dma_encode_transfer_count(N_CHAN*2),
                                      true); // can start now...
                // At this point, the data bytes are ready to be sent via SPI0,
                // so we can signal to the external supervisor device that there
                // is data to collect.
                assert_data_ready();
                // It is up to the external device to collect all of the data
                // by selecting the Pico2 as a slave SPI device and clocking out
                // all of the bytes.
                uint64_t timeout = time_us_64() + timeout_period_us;
                // Wait for selection by the SPI-master device.
                // If this does not happen within a reasonable time,
                // we presume that the SPI-master device is not present
                // or not paying attention to the DATA_RDY signal,
                // so we cancel the data transfer.
                while (gpio_get(SPI0_CSn_PIN)) {
                    if (time_reached(timeout)) { goto timed_out; }
                }
                enable_RTDP_transceiver();
                // Wait for the data to be clocked out.
                while (dma_channel_is_busy(dma_spi0_tx)) {
                    if (time_reached(timeout)) { goto timed_out; }
                }
                // Wait for deselection by the SPI-master device.
                while (!gpio_get(SPI0_CSn_PIN)) {
                    if (time_reached(timeout)) { goto timed_out; }
                }
                // If we arrive here then the data has been transferred through
                // the SPI peripheral
                goto finish;
            timed_out:
                spi_deinit(spi0);
                dma_channel_cleanup(dma_spi0_tx);
                dma_channel_cleanup(dma_spi0_rx);
                my_spi_is_initialized = false;
            finish:
                disable_RTDP_transceiver();
                clear_data_ready();
                RTDP_status = RTDP_IDLE;
            } // end new scope
            break;
        case RTDP_STOP:
            spi_deinit(spi0);
            dma_channel_cleanup(dma_spi0_tx);
            dma_channel_cleanup(dma_spi0_rx);
            my_spi_is_initialized = false;
            clear_data_ready();
            RTDP_status = RTDP_IDLE;
            active = false;
            break;
        default:
            {} // do nothing for any other command value
        }
    } // end while
    dma_channel_unclaim(dma_spi0_tx);
    dma_channel_unclaim(dma_spi0_rx);
} // end void core1_service_RTDP()

//
// core0 services the main sampling activity.
//

void __no_inline_not_in_flash_func(sample_channels)(void)
// Sample the analog channels periodically and store the data in SRAM.
//
// For mode=0, we will consider that the trigger event is immediate, at sample 0,
// and the record will stop after a specified number of samples.
// So long as the record does not wrap around, the oldest sample set will start at
// byte address 0.
//
// For mode=1, we will start sampling into the SRAM circular buffer
// for an indefinite number of samples, while waiting for the trigger event.
// Once the trigger event happens, we will continue the record for a specified
// number of samples.  Because we do not keep a record of the number of times
// that the SRAM address wraps around, we just assume that the oldest sample
// starts at the next word address to be used to store a sample.
//
{
    // Get configuration data from virtual registers.
    uint16_t period_us = (uint16_t)vregister[0];
    uint8_t mode = (uint8_t)vregister[3];
# define TRIGGER_IMMEDIATE 0
# define TRIGGER_ON_EVENT  1
    bool service_RTDP = (vregister[4] != 0) && (period_us >= 2);
    uint cmd = RTDP_STOP;
    if (service_RTDP) {
        queue_init(&RTDP_command_fifo, sizeof(uint), RTDP_FIFO_LENGTH);
    }
    //
    release_eventn_line();
    next_fullword_index_in_data = 0; // Start afresh, at index 0.
    fullword_index_has_wrapped_around = 0;
    uint8_t post_event = 0;
    uint16_t samples_remaining = (uint16_t)vregister[2];
    // Start up the PIO program that happens to block
    // until a word is put into its TX FIFO
    bu79100g_eight_read_program_init(pio0, 0, pio_offset_for_8_read_program);
    //
    // Main loop for sampling.
    //
    // Note that when we are asking for a single set of samples,
    // we the loop will actually take two sample sets because the
    // event does not occur until after the first sample set and
    // then the samples_remaining count will be reduced to zero
    // in the following pass of the loop.
    // This is actually handy for interacting with the BU79100G chips
    // because the first conversion following chip-select going low
    // is not valid.
    //
    // There are two variants of the main loop, one as fast as we can,
    // and the other paced by the system timer.
    //
    did_not_keep_up_during_sampling = 0; // Presume that we will be fast enough.
    if (period_us < 2) {
		// Run the sampling process as fast as the PIO will allow.
		// This should give us about 1MSps.
        // Note that we do not have enough time to service the RTDP,
        // even if it is requested to do so.
        sampling_LED_ON();
        while (samples_remaining > 0) {
            // Begin taking the analog sample set via the PIO.
		    pio_sm_put_blocking(pio0, 0, 1);
            uint32_t* here = &data[next_fullword_index_in_data];
            // While the PIO starts sampling process and begins
            // getting data from the BU79100G chips,
            // check the state of the EVENTn line for a trigger.
            if (post_event) {
                // Trigger event has happened.
                samples_remaining--;
            } else {
                // We need to decide about trigger event.
                if (mode == TRIGGER_IMMEDIATE) {
                    post_event = 1;
                    assert_eventn();
                } else {
				    // Waiting for EVENTn.
                    if (read_system_eventn_line() == 0) {
                        post_event = 1;
                        // We also assert the EVENTn signal low,
                        // to show that we have seen it.
                        assert_eventn();
                    }
                }
            }
            // Read all 8 ADC chips via the PIO.
            // Each of four 32-bit words coming from the PIO's RX FIFO
            // will hold one 4-bit nybble for each of eight ADC bit streams.
            *here = pio_sm_get_blocking(pio0, 0);
		    *(here+1) = pio_sm_get_blocking(pio0, 0);
		    *(here+2) = pio_sm_get_blocking(pio0, 0);
		    *(here+3) = pio_sm_get_blocking(pio0, 0);
            // Point to the next available fullword index.
            next_fullword_index_in_data += 4;
            if (next_fullword_index_in_data >= N_FULLWORDS) {
                next_fullword_index_in_data -= N_FULLWORDS;
                fullword_index_has_wrapped_around = 1;
            }
        } // end while (main sampling loop, fast variant)
        sampling_LED_OFF();
	} else {
		// For sample periods greater than 1microsecond,
		// the loop is paced by the system clock.
        //
        // We also have enough time to service the RTDP, if it is requested.
        if (service_RTDP) {
            multicore_launch_core1(core1_service_RTDP);
        }
        uint64_t timeout = time_us_64() + period_us;
        while (samples_remaining > 0) {
            sampling_LED_ON();
            raise_flag_pin(); // to allow timing via a logic probe.
            //
            // Take the analog sample set.
            // Read all 8 ADC chips via the PIO.
            // Each of four 32-bit words coming from the PIO's RX FIFO
            // will hold one 4-bit nybble for each of eight ADC bit streams.
		    pio_sm_put_blocking(pio0, 0, 1);
            uint32_t* here = &data[next_fullword_index_in_data];
            *here = pio_sm_get_blocking(pio0, 0);
		    *(here+1) = pio_sm_get_blocking(pio0, 0);
		    *(here+2) = pio_sm_get_blocking(pio0, 0);
		    *(here+3) = pio_sm_get_blocking(pio0, 0);
            //
            if (service_RTDP
                && (queue_is_empty(&RTDP_command_fifo))
                && RTDP_status == RTDP_IDLE) {
                RTDP_data_words[0] = *here;
                RTDP_data_words[1] = *(here+1);
                RTDP_data_words[2] = *(here+2);
                RTDP_data_words[3] = *(here+3);
                cmd = RTDP_ADVERTISE_NEW_DATA;
                queue_add_blocking(&RTDP_command_fifo, &cmd);
            }
            //
            if (post_event) {
                // Trigger event has happened.
                samples_remaining--;
            } else {
                // We need to decide about trigger event.
                if (mode == TRIGGER_IMMEDIATE) {
                    post_event = 1;
                    assert_eventn();
                } else {
				    // Waiting for EVENTn.
                    if (read_system_eventn_line() == 0) {
                        post_event = 1;
                        // We also assert the EVENTn signal low,
                        // to show that we have seen it.
                        assert_eventn();
                    }
                }
            }
            // Point to the next available fullword index.
            next_fullword_index_in_data += 4;
            if (next_fullword_index_in_data >= N_FULLWORDS) {
                next_fullword_index_in_data -= N_FULLWORDS;
                fullword_index_has_wrapped_around = 1;
            }
            lower_flag_pin();
            sampling_LED_OFF();
            bool late_flag = time_reached(timeout);
            // If we arrive late for the timer, for even one sample set, set the global flag.
            if (late_flag) {
			    did_not_keep_up_during_sampling = 1;
		    } else {
			    busy_wait_until(timeout);
		    }
		    timeout += period_us;
        } // end while (main sampling loop, slow variant)
        //
        if (service_RTDP) {
            while (queue_is_full(&RTDP_command_fifo)) {
                tight_loop_contents();
            }
            cmd = RTDP_STOP;
            queue_add_blocking(&RTDP_command_fifo, &cmd);
            while ((queue_is_full(&RTDP_command_fifo))
                   || (RTDP_status == RTDP_BUSY)) {
                // We wait for the last RTDP command to finish.
                tight_loop_contents();
            }
            queue_free(&RTDP_command_fifo);
            multicore_reset_core1();
        }
	}
    //
    // Note that we leave the bits in their packed arrangement,
    // just as they were collected from the PIO.
    //
} // end void sample_channels()

void sample_channels_once()
{
    // We temporarily override some of the registers to make this happen.
    int ticks_save = vregister[0];
    int mode_save = vregister[3];
    int samples_remaining_save = vregister[2];
    //
    vregister[0] = 10; // Time enough to do a full scan.
    vregister[3] = 0; // Immediate mode.
    vregister[2] = 1; // One sample set.
    sample_channels();
    //
    // Restore register values.
    vregister[0] = ticks_save;
    vregister[3] = mode_save;
    vregister[2] = samples_remaining_save;
    return;
} // end sample_channels_once()

#define NSTRBUF1 128
char str_buf1[NSTRBUF1];
#define NSTRBUF2 16
char str_buf2[NSTRBUF2];

char* sample_set_to_str(uint32_t n)
{
    uint16_t values[N_CHAN] = {0, 0, 0, 0, 0, 0, 0, 0};
    // Start with index of oldest sample, then move to selected sample.
    uint32_t word_index = oldest_fullword_index_in_data() + 4*n;
    // Assume that the fullword sets in the data wrap neatly.
	if (word_index > N_FULLWORDS) { word_index -= N_FULLWORDS; }
    unpack_sample_set(&(data[word_index]), values);
    snprintf(str_buf1, NSTRBUF1, "%d", values[0]);
    for (uint8_t ch=1; ch < N_CHAN; ch++) {
        snprintf(str_buf2, NSTRBUF2, " %d", values[ch]);
        strncat(str_buf1, str_buf2, NSTRBUF2);
    }
    return str_buf1;
}

char* mem_dump_to_str(uint32_t addr)
// Write a 32-byte page of sample data into the buffer as hex digits
// representing the 16-bit converted samples. Use big-endian format.
// Finally, return a pointer to the buffer.
{
    uint16_t values[N_CHAN] = {0, 0, 0, 0, 0, 0, 0, 0};
    // Assume that the byte address is correctly aligned.
	uint32_t word_index = addr / 4;
    unpack_sample_set(&(data[word_index]), values);
    uint8_t high_byte = (uint8_t) ((values[0] & 0xff00) >> 8);
    uint8_t low_byte = (uint8_t) (values[0] & 0x00ff);
    snprintf(str_buf1, NSTRBUF1, "%02x%02x", high_byte, low_byte);
    for (uint8_t ch=1; ch < N_CHAN; ch++) {
        high_byte = (uint8_t) ((values[ch] & 0xff00) >> 8);
        low_byte = (uint8_t) (values[ch] & 0x00ff);
        snprintf(str_buf2, NSTRBUF2, "%02x%02x", high_byte, low_byte);
        strncat(str_buf1, str_buf2, NSTRBUF2);
    }
    for (uint8_t ch=0; ch < N_CHAN; ch++) values[ch] = 0;
    word_index += 4;
    unpack_sample_set(&(data[word_index]), values);
    for (uint8_t ch=0; ch < N_CHAN; ch++) {
        high_byte = (uint8_t) ((values[ch] & 0xff00) >> 8);
        low_byte = (uint8_t) (values[ch] & 0x00ff);
        snprintf(str_buf2, NSTRBUF2, "%02x%02x", high_byte, low_byte);
        strncat(str_buf1, str_buf2, NSTRBUF2);
    }
	return str_buf1;
}

// For incoming serial comms
#define NBUFA 80
char bufA[NBUFA];

int getstr(char* buf, int nbuf)
// Read (without echo) a line of characters into the buffer,
// stopping when we see a new-line character.
// Returns the number of characters collected,
// excluding the terminating null character.
{
	memset(buf, '\0', nbuf);
    int i = 0;
    char c;
    uint8_t done = 0;
    while (!done) {
        c = getc(stdin);
        if (c != '\n' && c != '\r' && c != '\b' && i < (nbuf-1)) {
            // Append a normal character.
            buf[i] = c;
            i++;
        }
        if (c == '\n') {
            done = 1;
            buf[i] = '\0';
        }
        if (c == '\b' && i > 0) {
            // Backspace.
            i--;
        }
    }
    return i;
} // end getstr()

int trim_string(char *str)
// Trim space characters from the start and end of the string.
// We assume that the string is properly null terminated.
// Returns the number of characters in the trimmed string, excluding the terminating '\0'.
{
	int len = strlen(str);
	if (len == 0) return 0;
	int start = 0;
	while (isspace((unsigned char)str[start])) {
		start += 1;
	}
	if (start == len) {
	    // There are no non-space characters left.
		str[0] = '\0';
		return 0;
	}
	// At this point, we have at least one non-space character.
	if (start > 0) {
		// Move all remaining characters.
		memmove(str, str+start, len-start);
		len -= start;
	}
	str[len] = '\0';
	int last = len - 1;
	while ((last >= 0) && isspace((unsigned char)str[last])) {
		str[last] = '\0';
		last -= 1;
	}
	return last+1; // final string length
}

void interpret_command(char* cmdStr)
// The first character in the string specifies the command.
// Any following text is interpreted as delimiter-separated integers
// and used as arguments for the command.
// A successful command should echo the first character,
// followed by any results as the message.
// A command that does not do what is expected should return a message
// that includes the word "error".
{
    char* token_ptr;
    const char* sep_tok = ", ";
    uint8_t i;
	int16_t v;
    // printf("DEBUG: DAQ MCU cmdStr=\"%s\"", cmdStr);
    if (!override_led) gpio_put(LED_PIN, 1); // To indicate start of interpreter activity.
    switch (cmdStr[0]) {
	case 'v':
		// Report version string and (some) configuration details.
		uint f_clk_sys = frequency_count_khz(CLOCKS_FC0_SRC_VALUE_CLK_SYS);
		printf("%s %dxBU79100 %d kHz ok\n", VERSION_STR, n_adc_chips, f_clk_sys);
		break;
	case 'L':
		// Turn LED on or off.
		// Turning the LED on by command overrides its use
		// as an indicator of interpreter activity.
		token_ptr = strtok(&cmdStr[1], sep_tok);
		if (token_ptr) {
			// Found some non-blank text; assume on/off value.
			// Use just the least-significant bit.
			i = (uint8_t) (atoi(token_ptr) & 1);
			gpio_put(LED_PIN, i);
			override_led = i;
			printf("%d ok\n", i);
		} else {
			// There was no text to give a value.
			printf("fail: no value\n");
		}
		break;
	case 'n':
		// Report number of virtual registers.
		printf("%d ok\n", NUMREG);
		break;
    case 'r':
        // Report a selected register value.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text, assume register number.
            i = (uint8_t) atoi(token_ptr);
            if (i < NUMREG) {
                v = vregister[i];
                printf("%d ok\n", v);
            } else {
                printf("fail: invalid register.\n");
            }
        } else {
            printf("fail: no register specified.\n");
        }
        break;
    case 's':
        // Set a selected register value.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text; assume register number.
            i = (uint8_t) atoi(token_ptr);
            if (i < NUMREG) {
                token_ptr = strtok(NULL, sep_tok);
                if (token_ptr) {
                    // Assume text is value for register.
                    v = atoi(token_ptr);
                    if (i != 1) {
                        // Accept user-specified value for most registers.
                        vregister[i] = v;
                        printf("reg[%u] %d ok\n", i, v);
                    } else {
                        // Ignore user input for the number of channels.
                        printf("reg[%u] %d ok\n", i, N_CHAN);
                    }
                } else {
                    printf("fail: no value given.\n");
                }
            } else {
                printf("fail: invalid register.\n");
            }
        } else {
            printf("fail: no register specified.\n");
        }
        break;
    case 'F':
        // Set the values of the registers to those values hard-coded
        // into this firmware.  A factory default, so to speak.
        set_registers_to_original_values();
        printf("vregisters reset ok\n");
        break;
    case 'b':
        // Byte size of sample set.
        printf("%d ok\n", N_CHAN*2);
        break;
    case 'm':
        // Maximum number of sample sets that can be stored.
        printf("%d ok\n", MAX_N_SAMPLES);
        break;
    case 'T':
        // Total bytes assigned to sample storage.
        printf("%d ok\n", N_FULLWORDS*4);
        break;
    case 'a':
        // Byte index (within sample data storage) of the oldest sample.
        printf("%d ok\n", ((fullword_index_has_wrapped_around) ?
                           next_fullword_index_in_data*4 : 0));
        break;
    case 'N':
        // Size of data storage in 32-byte pages.
        printf("%d ok\n", N_FULLWORDS/8);
        break;
    case 'M':
        // Page of bytes (in big-endian format) representing
        // two sample sets, each with 8x16-bit values.
        // Start at the specified byte-index within the stored data.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text, assume byte-index.
            uint32_t addr = (uint32_t) atoi(token_ptr);
            printf("%s ok\n", mem_dump_to_str(addr));
        } else {
            printf("fail: no byte-index specified.\n");
        }
        break;
    case 'g':
        // Start the sampling process.
        // What happens next, and when it happens, depends on the
        // register settings and external signals.
        printf("start sampling ok\n");
        // The task takes an indefinite time,
        // so let the COMMS_MCU know via busy# pin.
        assert_not_ready();
        sample_channels();
        assert_ready();
        break;
    case 'k':
        // Report the value of the keeping-up flag.
        printf("%u ok\n", did_not_keep_up_during_sampling);
        break;
    case 'I':
        // Immediately take a single sample set and report values.
        sample_channels_once();
        // Despite the name saying that the channels are sampled once,
        // they are actually sampled twice and only the second set is
        // valid.  We return that second sample set, at index 1.
        printf("%s ok\n", sample_set_to_str(1));
        break;
    case 'P':
        // Report the selected sample set.
        // An index of 0 refers to the oldest sample set.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text, assume sample index.
            uint32_t ii = (uint32_t) atol(token_ptr);
            printf("%s ok\n", sample_set_to_str(ii));
        } else {
            printf("fail: no index given.\n");
        }
        break;
    case 'z':
        // Release the EVENT# line.
        // Presumably this line has been help low following
        // a trigger event during the sampling process.
        release_eventn_line();
        printf("event line released ok\n");
        break;
	default:
		printf("fail: Unknown command %c\n", cmdStr[0]);
    }
    if (!override_led) gpio_put(LED_PIN, 0); // To indicate end of interpreter activity.
} // end interpret_command()


int main()
{
	set_registers_to_original_values();
    stdio_init_all();
	uart_set_baudrate(uart0, 230400);
	// Attempt to discard any characters sitting the UART already.
	while (uart_is_readable_within_us(uart0, 100)) {
		__unused char junkc = uart_getc(uart0);
	}
	//
    // Some information for picotool.
	//
    bi_decl(bi_program_description(VERSION_STR));
    bi_decl(bi_1pin_with_name(LED_PIN, "LED output pin"));
    bi_decl(bi_1pin_with_name(TIMING_FLAG_PIN, "Flag output pin for timing measurements"));
    bi_decl(bi_1pin_with_name(READY_PIN, "Ready/Busy# output pin"));
    bi_decl(bi_1pin_with_name(Pico2_EVENT_PIN, "Pico2 EVENT output pin"));
    bi_decl(bi_1pin_with_name(SYSTEM_EVENTn_PIN, "System EVENTn input/output pin"));
    bi_decl(bi_1pin_with_name(PIO_CSn_PIN, "PIO0 chip select pin"));
    bi_decl(bi_1pin_with_name(PIO_CLK_PIN, "PIO0 clock output pin"));
    bi_decl(bi_1pin_with_name(PIO_RX0_PIN, "PIO0 data0 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX1_PIN, "PIO0 data1 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX2_PIN, "PIO0 data2 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX3_PIN, "PIO0 data3 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX4_PIN, "PIO0 data4 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX5_PIN, "PIO0 data5 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX6_PIN, "PIO0 data6 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX7_PIN, "PIO0 data7 input pin"));
    bi_decl(bi_1pin_with_name(SPI0_CSn_PIN, "SPI0 slave-select input pin"));
    bi_decl(bi_1pin_with_name(SPI0_SCK_PIN, "SPI0 clock input pin"));
    bi_decl(bi_1pin_with_name(SPI0_TX_PIN, "SPI0 data output pin"));
    bi_decl(bi_1pin_with_name(RTDP_DE_PIN, "RTDP transmit driver enable pin"));
    bi_decl(bi_1pin_with_name(RTDP_REn_PIN, "RTDP read serial-clock enable pin"));
    bi_decl(bi_1pin_with_name(DATA_RDY_PIN, "RTDP data-ready output pin"));
	//
	// Flash LED twice at start up.
	//
    gpio_init(LED_PIN);
    gpio_set_dir(LED_PIN, GPIO_OUT);
	sampling_LED_ON(); sleep_ms(500);
	sampling_LED_OFF(); sleep_ms(500);
	sampling_LED_ON(); sleep_ms(500);
	sampling_LED_OFF();
	//
	// Establish the PIO state machine program(s) to talk to the BU79100G ADC chips.
	pio_offset_for_8_read_program = pio_add_program(pio0, &bu79100g_eight_read_program);
	//
	// No longer using Pico2_EVENT_PIN.
	// gpio_init(Pico2_EVENT_PIN);
	// gpio_set_dir(Pico2_EVENT_PIN, GPIO_OUT);
    // gpio_disable_pulls(Pico2_EVENT_PIN);
	//
	// We initially sense the system EVENTn line.
	// Later, we may/will assert a low signal on it.
	gpio_init(SYSTEM_EVENTn_PIN);
	gpio_set_dir(SYSTEM_EVENTn_PIN, GPIO_IN);
    gpio_pull_up(SYSTEM_EVENTn_PIN);
	release_eventn_line(); // redundant
	//
    gpio_init(TIMING_FLAG_PIN);
    gpio_set_dir(TIMING_FLAG_PIN, GPIO_OUT);
    gpio_disable_pulls(TIMING_FLAG_PIN);
    lower_flag_pin();
    did_not_keep_up_during_sampling = 0;
    //
    // Set up the Real-Time Data Port.
    // First, the RS485 transceiver.
    gpio_init(RTDP_DE_PIN);
    gpio_set_dir(RTDP_DE_PIN, GPIO_OUT);
    gpio_disable_pulls(RTDP_DE_PIN);
    gpio_init(RTDP_REn_PIN);
    gpio_set_dir(RTDP_REn_PIN, GPIO_OUT);
    gpio_disable_pulls(RTDP_REn_PIN);
    disable_RTDP_transceiver();
    // Second, the DATA_RDY signal.
    gpio_init(DATA_RDY_PIN);
    gpio_set_dir(DATA_RDY_PIN, GPIO_OUT);
    gpio_disable_pulls(DATA_RDY_PIN);
    clear_data_ready();
    // Third, the SPI module as a slave, for transmit only.
    // We assign the IO pin functions here but delay the module
    // initialization until we actually want to use it.
    gpio_set_function(SPI0_CSn_PIN, GPIO_FUNC_SPI);
    gpio_set_function(SPI0_SCK_PIN, GPIO_FUNC_SPI);
    gpio_set_function(SPI0_TX_PIN, GPIO_FUNC_SPI);
    //
	// Signal to the COMMS MCU that we are ready.
	//
    gpio_init(READY_PIN);
    gpio_set_dir(READY_PIN, GPIO_OUT);
    gpio_disable_pulls(READY_PIN);
	assert_ready();
    //
	// Enter the command loop.
    while (1) {
        // Characters are not echoed as they are typed.
        // Backspace deleting is allowed.
        // NL (Ctrl-J) signals end of incoming string.
        int m = getstr(bufA, NBUFA);
		m = trim_string(bufA);
        // Note that the cmd string may be of zero length,
        // with the null character in the first place.
        // If that is the case, do nothing with it
		// but just reply with a newline character.
        if (m > 0) {
            interpret_command(bufA);
        } else {
			printf("error: empty command\n");
		}
    }
    return 0;
}

