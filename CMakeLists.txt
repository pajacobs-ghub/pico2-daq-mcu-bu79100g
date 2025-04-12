cmake_minimum_required(VERSION 3.18)
set(PICO_BOARD pico2)

if (DEFINED ENV{PICO_SDK_PATH} AND (NOT PICO_SDK_PATH))
    set(PICO_SDK_PATH $ENV{PICO_SDK_PATH})
    message("Using PICO_SDK_PATH from environment ('${PICO_SDK_PATH}')")
endif ()

set(PICO_SDK_INIT_CMAKE_FILE ${PICO_SDK_PATH}/pico_sdk_init.cmake)
include(${PICO_SDK_INIT_CMAKE_FILE})
message("Raspberry Pi Pico SDK version is ${PICO_SDK_VERSION_STRING}")

project(tcd1304_reader C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)
# Initialize the SDK
pico_sdk_init()

add_compile_options(-Wall
        -Wno-format # int != int32_t because gcc has int32_t as long int
        )

add_executable(mcp3301_pio)

pico_generate_pio_header(mcp3301_pio ${CMAKE_CURRENT_LIST_DIR}/mcp3301.pio)

target_sources(mcp3301_pio PRIVATE mcp3301_pio.c)

# pull in common dependencies
target_link_libraries(mcp3301_pio PRIVATE
	pico_stdlib 
	hardware_pio
	hardware_timer
	hardware_spi
	)

# enable uart0
pico_enable_stdio_uart(mcp3301_pio 1)

# create map/bin/hex file etc.
pico_add_extra_outputs(mcp3301_pio)

# add url via pico_set_program_url
pico_set_program_url(mcp3301_pio "https://github.com/pajacobs-ghub/mcp3301-adc-with-pio")

