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

add_executable(pico2_daq_mcp3301)

pico_generate_pio_header(pico2_daq_mcp3301 ${CMAKE_CURRENT_LIST_DIR}/mcp3301.pio)

target_sources(pico2_daq_mcp3301 PRIVATE pico2_daq_mcp3301.c)

# pull in common dependencies
target_link_libraries(pico2_daq_mcp3301 PRIVATE
	pico_stdlib 
	hardware_pio
	hardware_timer
	hardware_spi
	)

# enable uart0
pico_enable_stdio_uart(pico2_daq_mcp3301 1)

# create map/bin/hex file etc.
pico_add_extra_outputs(pico2_daq_mcp3301)

# add url via pico_set_program_url
pico_set_program_url(pico2_daq_mcp3301 "https://github.com/pajacobs-ghub/mcp3301-adc-with-pio")

