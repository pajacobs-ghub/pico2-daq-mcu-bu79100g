// mcp3301_pio.c
// PIO example code (to be) mostly copied from here
// https://github.com/raspberrypi/pico-examples/pio/spi/
//
// PJ 2025-04-06: simple interpreter without any pio interaction
//
#include "pico/stdlib.h"
#include "hardware/gpio.h"
#include "hardware/pio.h"
#include "hardware/uart.h"
#include "pico/binary_info.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <ctype.h>

#define VERSION_STR "v0.3 2025-04-07 Pico2 with MCP3301 ADC"

// Names for the IO pins.
const uint READY_PIN = 22;
const uint Pico2_EVENT_PIN = 3;
const uint SYSTEM_EVENTn_PIN = 2;

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
#define NWORDS 0x00020000
int16_t data[NWORDS];
uint32_t next_word_index_in_data;
uint8_t word_index_has_wrapped_around;

uint8_t event_n;
uint8_t did_not_keep_up_during_sampling;

// Parameters controlling the device are stored in virtual config registers.
#define NUMREG 7
int16_t vregister[NUMREG]; // working copy in SRAM

void set_registers_to_original_values()
{
    vregister[0] = 1250; // sample period in timer ticks
    vregister[1] = 4;    // number of channels to sample 1, 2 or 4; (3 does not wrap neatly)
    vregister[2] = 128;  // number of samples in record after trigger event
    vregister[3] = 0;    // trigger mode 0=immediate, 1=internal, 2=external
    vregister[4] = 0;    // trigger channel for internal trigger
    vregister[5] = 100;  // trigger level as a signed integer
    vregister[6] = 1;    // trigger slope 0=sample-below-level 1=sample-above-level
}

uint32_t max_n_samples(void)
{
    uint8_t n_chan = (uint8_t)vregister[1];
    return NWORDS / n_chan;
}

uint32_t oldest_word_index_in_data()
{
    return (word_index_has_wrapped_around) ? next_word_index_in_data : 0;
}

void sample_channels(void)
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
    uint16_t ticks = (uint16_t)vregister[0];
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
    // FIX-ME adc0_init();
    next_word_index_in_data = 0; // Start afresh, at index 0.
    word_index_has_wrapped_around = 0;
    uint8_t post_event = 0;
    uint16_t samples_remaining = (uint16_t)vregister[2];
    did_not_keep_up_during_sampling = 0; // Presume that we will be fast enough.
    // FIX-ME timerA0_init(ticks); // period=ticks*0.8us
    // FIX-ME timerA0_wait();
    //
    while (samples_remaining > 0) {
        sampling_LED_ON();
        // Following flag will be set to 0 if we finish sampling before timer overflows.
        uint8_t late_flag = 1;
        // FIX-ME Take the analog sample set.
        for (uint8_t ch=0; ch < n_chan; ch++) {
            res[ch] = (int16_t)0; // 16-bit value only
        }
        // Save the sample for later.
        for (uint8_t ch=0; ch < n_chan; ch++) {
            data[next_word_index_in_data+ch] = res[ch];
        }
        // Point to the next available SRAM address.
        next_word_index_in_data += n_chan;
        if (next_word_index_in_data >= NWORDS) {
            next_word_index_in_data -= NWORDS;
            word_index_has_wrapped_around = 1;
        }
        sampling_LED_OFF();
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
        // Wait for timer overflow.
/*
        while (!(TCA0.SINGLE.INTFLAGS & TCA_SINGLE_OVF_bm)) {
            // __builtin_avr_wdr();
            // We have arrived before the timer overflowed for this sample period.
            late_flag = 0;
        }
        // We reset the interrupt flag for the timer but leave the timer ticking
        // so that we have accurate periods.
*/
        // If we arrive late for the timer, for even one sample set, set the global flag.
        if (late_flag) did_not_keep_up_during_sampling = 1;
    } // end while
    // FIX-ME timerA0_close();
    // FIX-ME adc0_close();
} // end void sample_channels()

void sample_channels_once()
{
    // We temporarily override some of the registers to make this happen.
    uint16_t ticks_save = (uint16_t)vregister[0];
    uint8_t mode_save = (uint8_t)vregister[3];
    uint16_t samples_remaining_save = (uint16_t)vregister[2];
    //
    vregister[0] = (uint16_t)200; // Time enough to do a full scan.
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
    uint32_t index = oldest_word_index_in_data();
    index += n_chan * n;
    // Assume that the word sets in the data wrap neatly.
	if (index > NWORDS) { index -= NWORDS; }
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
		printf("v %s\n", VERSION_STR);
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
	//
    // Some information for picotool.
	//
    bi_decl(bi_program_description(VERSION_STR));
    bi_decl(bi_1pin_with_name(LED_PIN, "LED output pin"));
    bi_decl(bi_1pin_with_name(READY_PIN, "Ready/Busy# output pin"));
    bi_decl(bi_1pin_with_name(Pico2_EVENT_PIN, "Pico2 EVENT output pin"));
    bi_decl(bi_1pin_with_name(SYSTEM_EVENTn_PIN, "Sense EVENT input pin"));
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

