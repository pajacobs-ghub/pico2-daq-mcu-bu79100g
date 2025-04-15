// pico2_daq_mcp3301.c
//
// RP2350 Pico2 board as the DAQ-MCU, getting data from a single MCP3301.
//
// PJ 2025-04-06: simple interpreter without any pio interaction
//    2025-04-09: data being collected from MCP3301 chip 0 via SPI0.
//    2025-04-13: have the PIO working to collect MCP3301 0 data.
//    2025-04-14: move PIO-RX pin so that we have room for 8 RX pins.
//    2025-04-15: implement code for reading 8 MCP3301 chips.
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
#include "mcp3301.pio.h"

#define VERSION_STR "v0.8 2025-04-15 Pico2 as DAQ MCU"
// #define EIGHT_MCP3301
#ifdef EIGHT_MCP3301
const uint n_mcp3301_chips = 8;
#else
const uint n_mcp3301_chips = 1;
#endif

// Names for the IO pins.
const uint READY_PIN = 22;
const uint FLAG_PIN = 26;
const uint Pico2_EVENT_PIN = 3;
const uint SYSTEM_EVENTn_PIN = 2;
const uint PIO_CSn_PIN = 5;
const uint PIO_CLK_PIN = 6;
const uint PIO_RX0_PIN = 7;
#ifdef EIGHT_MCP3301
const uint PIO_RX1_PIN = 8;
const uint PIO_RX2_PIN = 9;
const uint PIO_RX3_PIN = 10;
const uint PIO_RX4_PIN = 11;
const uint PIO_RX5_PIN = 12;
const uint PIO_RX6_PIN = 13;
const uint PIO_RX7_PIN = 14;
#endif

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
	gpio_put(FLAG_PIN, 1);
}

static inline void lower_flag_pin()
{
	gpio_put(FLAG_PIN, 0);
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

// A place for the current samples.
#define MAXNCHAN 4
int16_t res[MAXNCHAN];

// A place to collect the full record.
#define N_HALFWORDS 0x00020000
int16_t data[N_HALFWORDS];
uint32_t next_halfword_index_in_data;
uint8_t halfword_index_has_wrapped_around;

uint8_t event_n;
uint8_t did_not_keep_up_during_sampling;

// Parameters controlling the device are stored in virtual config registers.
#define NUMREG 7
int16_t vregister[NUMREG]; // working copy in SRAM

void set_registers_to_original_values()
{
    vregister[0] = 100;  // sample period in microseconds (timer ticks)
    vregister[1] = 4;    // number of channels to sample 1, 2 or 4; (3 does not fit neatly)
    vregister[2] = 128;  // number of samples in record after trigger event
    vregister[3] = 0;    // trigger mode 0=immediate, 1=internal, 2=external
    vregister[4] = 0;    // trigger channel for internal trigger
    vregister[5] = 100;  // trigger level as a signed integer
    vregister[6] = 1;    // trigger slope 0=sample-below-level 1=sample-above-level
}

static inline uint32_t max_n_samples(void)
{
    uint8_t n_chan = (uint8_t)vregister[1];
    return N_HALFWORDS / n_chan;
}

static inline uint32_t oldest_halfword_index_in_data()
{
    return (halfword_index_has_wrapped_around) ? next_halfword_index_in_data : 0;
}

static inline void unpack_nybbles_from_word(uint32_t word, uint16_t values[], uint least_bit) {
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
				values[rxi] |= 1 << (bin + least_bit);
			}
		}
	}
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
    uint8_t n_chan = (uint8_t)vregister[1];
    uint8_t mode = (uint8_t)vregister[3];
# define TRIGGER_IMMEDIATE 0
# define TRIGGER_INTERNAL 1
# define TRIGGER_EXTERNAL 2
    uint8_t trigger_chan = (uint8_t)vregister[4];
    int16_t trigger_level = vregister[5];
    uint8_t trigger_slope = (uint8_t)vregister[6];
    //
    release_event();
    next_halfword_index_in_data = 0; // Start afresh, at index 0.
    halfword_index_has_wrapped_around = 0;
    uint8_t post_event = 0;
    uint16_t samples_remaining = (uint16_t)vregister[2];
    did_not_keep_up_during_sampling = 0; // Presume that we will be fast enough.
    uint64_t timeout = time_us_64() + period_us;
    //
    //
    while (samples_remaining > 0) {
        sampling_LED_ON();
        raise_flag_pin(); // to allow timing via a logic probe.
        //
        // Take the analog sample set.
#		ifdef EIGHT_MCP3301
        // Read all 8 MCP3301 chips via the PIO.
        // Each of four 32-bit words coming from the PIO's RX FIFO 
        // will hold one 4-bit nybble for each of eight MCP3301 bit streams.
        uint16_t values[8] = {0, 0, 0, 0, 0, 0, 0, 0};
		pio_sm_put_blocking(pio0, 0, 1);
		uint32_t word = pio_sm_get_blocking(pio0, 0);
		unpack_nybbles_from_word(word, values, 12);
		word = pio_sm_get_blocking(pio0, 0);
		unpack_nybbles_from_word(word, values, 8);
		word = pio_sm_get_blocking(pio0, 0);
		unpack_nybbles_from_word(word, values, 4);
		word = pio_sm_get_blocking(pio0, 0);
		unpack_nybbles_from_word(word, values, 0);
        for (uint ch=0; ch < n_chan; ch++) {
			// The first couple of bits are not driven, only 13 should be kept.
			uint16_t value = values[ch] & 0x1fff;
			// We need to sign-extend the 13-bit number.
			if (value & 0x1000) { value |= 0xe000; }
			res[ch] = (int16_t)value;
		}
#       else
        // Read only MCP3301 chip 0.
		uint16_t value = 0;
		pio_sm_put_blocking(pio0, 0, 1);
		uint32_t pio_data = pio_sm_get_blocking(pio0, 0);
		value = (uint16_t)pio_data;
        // The first couple of bits are not driven, only 13 should be kept.
        value &= 0x1fff;
        // We need to sign-extend the 13-bit number.
        if (value & 0x1000) { value |= 0xe000; }
        res[0] = (int16_t)value;
        for (uint8_t ch=1; ch < n_chan; ch++) {
            res[ch] = (int16_t)0;
        }
#       endif
        // Save the sample set for later.
        for (uint8_t ch=0; ch < n_chan; ch++) {
            data[next_halfword_index_in_data+ch] = res[ch];
        }
        // Point to the next available halfword index.
        next_halfword_index_in_data += n_chan;
        if (next_halfword_index_in_data >= N_HALFWORDS) {
            next_halfword_index_in_data -= N_HALFWORDS;
            halfword_index_has_wrapped_around = 1;
        }
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
                int16_t s = res[trigger_chan];
                if ((trigger_slope == 1 && s >= trigger_level) ||
                    (trigger_slope == 0 && s <= trigger_level)) {
                    post_event = 1;
                    assert_event();
                } }
                break;
            case TRIGGER_EXTERNAL:
                if (read_system_event_pin() == 0) {
                    post_event = 1;
                }
            } // end switch
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
    vregister[0] = (uint16_t)20; // Time enough to do a full scan.
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
    uint8_t n_chan = (uint8_t)vregister[1];
    // Start with index of oldest sample, then move to selected sample.
    uint32_t index = oldest_halfword_index_in_data();
    index += n_chan * n;
    // Assume that the halfword sets in the data wrap neatly.
	if (index > N_HALFWORDS) { index -= N_HALFWORDS; }
	for (uint8_t ch=0; ch < n_chan; ch++) { res[ch] = data[index+ch]; }
    snprintf(str_buf1, NSTRBUF1, "%d", res[0]);
    for (uint8_t ch=1; ch < n_chan; ch++) {
        snprintf(str_buf2, NSTRBUF2, " %d", res[ch]);
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
		uint f_clk_sys = frequency_count_khz(CLOCKS_FC0_SRC_VALUE_CLK_SYS);
		printf("v %s %dxMCP3301 %d kHz\n", VERSION_STR, n_mcp3301_chips, f_clk_sys);
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
			printf("L %d\n", i);
		} else {
			// There was no text to give a value.
			printf("L error: no value\n");
		}
		break;
    case 'r':
        // Report a selected register value.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text, assume register number.
            i = (uint8_t) atoi(token_ptr);
            if (i < NUMREG) {
                v = vregister[i];
                printf("r %d\n", v);
            } else {
                printf("r error: invalid register.\n");
            }
        } else {
            printf("r error: no register specified.\n");
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
                    vregister[i] = v;
                    printf("s reg[%u] set to %d\n", i, v);
                } else {
                    printf("s error: no value given.\n");
                }
            } else {
                printf("s error: invalid register.\n");
            }
        } else {
            printf("s error: no register specified.\n");
        }
        break;
    case 'F':
        // Set the values of the registers to those values hard-coded
        // into this firmware.  A factory default, so to speak.
        set_registers_to_original_values();
        printf("F vregisters reset\n");
        break;
    case 'g':
        // Start the sampling process.
        // What happens next, and when it happens, depends on the
        // register settings and external signals.
        printf("g start sampling\n");
        // The task takes an indefinite time,
        // so let the COMMS_MCU know via busy# pin.
        assert_not_ready();
        sample_channels();
        assert_ready();
        break;
    case 'k':
        // Report the value of the keeping-up flag.
        printf("k %u\n", did_not_keep_up_during_sampling);
        break;
    case 'I':
        // Immediately take a single sample set and report values.
        sample_channels_once();
        printf("I %s\n", sample_set_to_str(0));
        break;
    case 'P':
        // Report the selected sample set for the configured channels.
        // An index of 0 refers to the oldest sample set.
        token_ptr = strtok(&cmdStr[1], sep_tok);
        if (token_ptr) {
            // Found some nonblank text, assume sample index.
            uint32_t ii = (uint32_t) atol(token_ptr);
            printf("P %s\n", sample_set_to_str(ii));
        } else {
            printf("P error: no index given.\n");
        }
        break;
    case 'z':
        // Release the EVENT# line.
        // Presumably this line has been help low following an internal
        // trigger event during the sampling process.
        release_event();
        printf("z event line released\n");
        break;
	default:
		printf("%c error: Unknown command\n", cmdStr[0]);
    }
    if (!override_led) gpio_put(LED_PIN, 0); // To indicate end of interpreter activity.
} // end interpret_command()


int main()
{
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
    bi_decl(bi_1pin_with_name(FLAG_PIN, "Flag output pin for timing measurements"));
    bi_decl(bi_1pin_with_name(READY_PIN, "Ready/Busy# output pin"));
    bi_decl(bi_1pin_with_name(Pico2_EVENT_PIN, "Pico2 EVENT output pin"));
    bi_decl(bi_1pin_with_name(SYSTEM_EVENTn_PIN, "Sense EVENT input pin"));
    bi_decl(bi_1pin_with_name(PIO_CSn_PIN, "PIO0 chip select pin"));
    bi_decl(bi_1pin_with_name(PIO_CLK_PIN, "PIO0 clock output pin"));
    bi_decl(bi_1pin_with_name(PIO_RX0_PIN, "PIO0 data0 input pin"));
#   ifdef EIGHT_MCP3301
    bi_decl(bi_1pin_with_name(PIO_RX1_PIN, "PIO0 data1 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX2_PIN, "PIO0 data2 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX3_PIN, "PIO0 data3 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX4_PIN, "PIO0 data4 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX5_PIN, "PIO0 data5 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX6_PIN, "PIO0 data6 input pin"));
    bi_decl(bi_1pin_with_name(PIO_RX7_PIN, "PIO0 data7 input pin"));
#   endif
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
	// Start the PIO state machine to talk to the MCP3301 chips.
	//
#   ifdef EIGHT_MCP3301
	uint offset = pio_add_program(pio0, &mcp3301_eight_read_program);
	mcp3301_eight_read_program_init(pio0, 0, offset);
#   else
	uint offset = pio_add_program(pio0, &mcp3301_one_read_program);
	mcp3301_one_read_program_init(pio0, 0, offset);
#   endif
	//
	// We output an event pin that gets buffered by the COMMS MCU
	// and reflected onto the system event line.
	// We sense that system event line, also.
	//
	gpio_init(Pico2_EVENT_PIN);
	gpio_set_dir(Pico2_EVENT_PIN, GPIO_OUT);
	gpio_init(SYSTEM_EVENTn_PIN);
	gpio_set_dir(SYSTEM_EVENTn_PIN, GPIO_IN);
	release_event();
	//
    gpio_init(FLAG_PIN);
    gpio_set_dir(FLAG_PIN, GPIO_OUT);
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

