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
//
#include "pico/stdlib.h"
#include "hardware/clocks.h"
#include "hardware/gpio.h"
#include "hardware/pio.h"
#include "hardware/uart.h"
#include "hardware/timer.h"
#include "hardware/spi.h"
#include "pico/binary_info.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <ctype.h>
#include "bu79100g.pio.h"

#define VERSION_STR "v0.12 2025-11-10 Pico2 as DAQ-MCU"
const uint n_adc_chips = 8;

// Names for the IO pins.
// A. For interaction with the PIC182Q71 COMMS-MCU.
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
const uint SPI0_CS_PIN = 17;
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

static inline void assert_event()
{
	gpio_put(Pico2_EVENT_PIN, 1);
}

static inline void release_event()
{
	gpio_put(Pico2_EVENT_PIN, 0);
}

static inline void raise_flag_pin()
{
	gpio_put(TIMING_FLAG_PIN, 1);
}

static inline void lower_flag_pin()
{
	gpio_put(TIMING_FLAG_PIN, 0);
}

static inline uint8_t read_system_event_pin()
{
	return (uint8_t) gpio_get(SYSTEM_EVENTn_PIN);
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

// Unlike the AVR DAQ firmware, we are going to hard-code the number of
// channels at 8 (because that is how we have to set up the PIO) and we
// are going to use uint16_t (a.k.a. half-words) as the sample type.
// Sample sets are going to be captured as sets of four uint32_t words,
// that may be decoded into 8 uint16_t half-words.

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
// [FIX-ME] It may be better to store parameters as int32_t on the Pico2.
// There seems to be no advantage to using 16 bits on a 32-bit MCU and
// there will be fewer surprises with full 32-bit values.
#define NUMREG 7
int16_t vregister[NUMREG]; // working copy in SRAM

void set_registers_to_original_values()
{
    // [FIX-ME] Maybe we should have the sample period be set by the PIO cycle.
    // The timer ticks resolution will be inadequate for a 1us sample period.
    vregister[0] = 10;     // sample period in microseconds (timer ticks)
    vregister[1] = N_CHAN; // number of channels to sample ia always 8.
    vregister[2] = 128;    // number of samples in record after trigger event
    vregister[3] = 0;      // trigger mode 0=immediate, 1=internal, 2=external
    vregister[4] = 0;      // trigger channel for internal trigger
    vregister[5] = 100;    // trigger level as a signed integer
    vregister[6] = 1;      // trigger slope 0=sample-below-level 1=sample-above-level
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

void __no_inline_not_in_flash_func(sample_channels)(void)
// Sample the analog channels periodically and store the data in SRAM.
//
// For mode=0, we will consider that the trigger event is immediate, at sample 0,
// and the record will stop after a specified number of samples.
// So long as the record does not wrap around, the oldest sample set will start at
// byte address 0.
//
// For mode=1 or 2, we will start sampling into the SRAM circular buffer
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
# define TRIGGER_INTERNAL 1
# define TRIGGER_EXTERNAL 2
    uint8_t trigger_chan = (uint8_t)vregister[4];
    uint16_t trigger_level = (uint16_t) vregister[5];
    uint8_t trigger_slope = (uint8_t)vregister[6];
    //
    release_event();
    next_fullword_index_in_data = 0; // Start afresh, at index 0.
    fullword_index_has_wrapped_around = 0;
    uint8_t post_event = 0;
    uint16_t samples_remaining = (uint16_t)vregister[2];
    did_not_keep_up_during_sampling = 0; // Presume that we will be fast enough.
    uint64_t timeout = time_us_64() + period_us;
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
        if (post_event) {
            // Trigger event has happened.
            samples_remaining--;
        } else {
            // We need to decide about trigger event.
            switch (mode) {
            case TRIGGER_IMMEDIATE:
                post_event = 1;
                assert_event();
                break;
            case TRIGGER_INTERNAL: {
                // Will only have time to do this if we are sampling slowly enough.
                uint16_t values[N_CHAN] = {0, 0, 0, 0, 0, 0, 0, 0};
                unpack_sample_set(here, values);
                uint16_t s = res[trigger_chan];
                if ((trigger_slope == 1 && s >= trigger_level) ||
                    (trigger_slope == 0 && s <= trigger_level)) {
                    post_event = 1;
                    assert_event();
                }
                }
                break;
            case TRIGGER_EXTERNAL:
                if (read_system_event_pin() == 0) {
                    post_event = 1;
                }
            } // end switch
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
    } // end while
} // end void sample_channels()

void sample_channels_once()
{
    // We temporarily override some of the registers to make this happen.
    uint16_t ticks_save = (uint16_t)vregister[0];
    uint8_t mode_save = (uint8_t)vregister[3];
    uint16_t samples_remaining_save = (uint16_t)vregister[2];
    //
    vregister[0] = (uint16_t)10; // Time enough to do a full scan.
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
		printf("v %s %dxBU79100 %d kHz ok\n", VERSION_STR, n_adc_chips, f_clk_sys);
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
			printf("L %d ok\n", i);
		} else {
			// There was no text to give a value.
			printf("L fail: no value\n");
		}
		break;
	case 'n':
		// Report number of virtual registers.
		printf("n %d ok\n", NUMREG);
		break;
    case 'r':
        // Report a selected register value.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text, assume register number.
            i = (uint8_t) atoi(token_ptr);
            if (i < NUMREG) {
                v = vregister[i];
                printf("r %d ok\n", v);
            } else {
                printf("r fail: invalid register.\n");
            }
        } else {
            printf("r fail: no register specified.\n");
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
                    v = (int16_t) atoi(token_ptr);
                    if (i != 1) {
                        // Accept user-specified value.
                        vregister[i] = v;
                        printf("s reg[%u] set to %d ok\n", i, v);
                    } else {
                        // Ignore user input.
                        printf("s reg[%u] set to %d ok\n", i, N_CHAN);
                    }
                } else {
                    printf("s fail: no value given.\n");
                }
            } else {
                printf("s fail: invalid register.\n");
            }
        } else {
            printf("s fail: no register specified.\n");
        }
        break;
    case 'F':
        // Set the values of the registers to those values hard-coded
        // into this firmware.  A factory default, so to speak.
        set_registers_to_original_values();
        printf("F vregisters reset ok\n");
        break;
    case 'g':
        // Start the sampling process.
        // What happens next, and when it happens, depends on the
        // register settings and external signals.
        printf("g start sampling ok\n");
        // The task takes an indefinite time,
        // so let the COMMS_MCU know via busy# pin.
        assert_not_ready();
        sample_channels();
        assert_ready();
        break;
    case 'k':
        // Report the value of the keeping-up flag.
        printf("k %u ok\n", did_not_keep_up_during_sampling);
        break;
    case 'I':
        // Immediately take a single sample set and report values.
        sample_channels_once();
        // Despite the name saying that the channels are sampled once,
        // they are actually sampled twice and only the second set is
        // valid.  We return that second sample set, at index 1.
        printf("I %s ok\n", sample_set_to_str(1));
        break;
    case 'P':
        // Report the selected sample set for the configured channels.
        // An index of 0 refers to the oldest sample set.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text, assume sample index.
            uint32_t ii = (uint32_t) atol(token_ptr);
            printf("P %s ok\n", sample_set_to_str(ii));
        } else {
            printf("P fail: no index given.\n");
        }
        break;
    case 'z':
        // Release the EVENT# line.
        // Presumably this line has been help low following an internal
        // trigger event during the sampling process.
        release_event();
        printf("z event line released ok\n");
        break;
	default:
		printf("%c fail: Unknown command\n", cmdStr[0]);
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
    bi_decl(bi_1pin_with_name(SYSTEM_EVENTn_PIN, "Sense EVENT input pin"));
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
	// Start the PIO state machine to talk to the BU79100G ADC chips.
	//
	uint offset = pio_add_program(pio0, &bu79100g_eight_read_program);
	bu79100g_eight_read_program_init(pio0, 0, offset);
	//
	// We output an event pin that gets buffered by the COMMS MCU
	// and reflected onto the system event line.
	// We sense that system event line, also.
	//
	gpio_init(Pico2_EVENT_PIN);
	gpio_set_dir(Pico2_EVENT_PIN, GPIO_OUT);
    gpio_disable_pulls(Pico2_EVENT_PIN);
	gpio_init(SYSTEM_EVENTn_PIN);
	gpio_set_dir(SYSTEM_EVENTn_PIN, GPIO_IN);
    gpio_disable_pulls(SYSTEM_EVENTn_PIN);
	release_event();
	//
    gpio_init(TIMING_FLAG_PIN);
    gpio_set_dir(TIMING_FLAG_PIN, GPIO_OUT);
    lower_flag_pin();
    did_not_keep_up_during_sampling = 0;
    //
	// Signal to the COMMS MCU that we are ready.
	//
    gpio_init(READY_PIN);
    gpio_set_dir(READY_PIN, GPIO_OUT);
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

