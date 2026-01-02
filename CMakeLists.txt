cmake_minimum_required(VERSION 3.18)
set(PICO_BOARD pico2)

if (DEFINED ENV{PICO_SDK_PATH} AND (NOT PICO_SDK_PATH))
    set(PICO_SDK_PATH $ENV{PICO_SDK_PATH})
    message("Using PICO_SDK_PATH from environment ('${PICO_SDK_PATH}')")
endif ()

set(PICO_SDK_INIT_CMAKE_FILE ${PICO_SDK_PATH}/pico_sdk_init.cmake)
include(${PICO_SDK_INIT_CMAKE_FILE})
message("Raspberry Pi Pico SDK version is ${PICO_SDK_VERSION_STRING}")

project(pico2_daq_bu79100g C CXX ASM)
set(CMAKE_C_STANDARD 11)
set(CMAKE_CXX_STANDARD 17)
# Initialize the SDK
pico_sdk_init()

add_compile_options(-Wall
        -Wno-format # int != int32_t because gcc has int32_t as long int
        )

add_executable(pico2_daq_bu79100g)

pico_generate_pio_header(pico2_daq_bu79100g ${CMAKE_CURRENT_LIST_DIR}/bu79100g.pio)

target_sources(pico2_daq_bu79100g PRIVATE pico2_daq_bu79100g.c)

# pull in common dependencies
target_link_libraries(pico2_daq_bu79100g PRIVATE
	pico_stdlib
    pico_multicore
    pico_util
	hardware_pio
	hardware_timer
	hardware_spi
    hardware_dma
	)

# enable uart0
pico_enable_stdio_uart(pico2_daq_bu79100g 1)

# create map/bin/hex file etc.
pico_add_extra_outputs(pico2_daq_bu79100g)

# add url via pico_set_program_url
pico_set_program_url(pico2_daq_bu79100g "https://github.com/pajacobs-ghub/pico2-daq-mcu-bu79100g/")

