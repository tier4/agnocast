cmake_minimum_required(VERSION 3.5)
project(agnocast_heaphook)

find_package(ament_cmake REQUIRED)

set(HEAPHOOK_SRC_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set(HEAPHOOK_BUILD_DIR ${HEAPHOOK_SRC_DIR}/target/release)
set(HEAPHOOK_OUTPUT ${HEAPHOOK_BUILD_DIR}/libagnocast_heaphook.so)

add_custom_target(build_agnocast_heaphook ALL
  COMMAND cargo build --release
  WORKING_DIRECTORY ${HEAPHOOK_SRC_DIR}
  BYPRODUCTS ${HEAPHOOK_OUTPUT}
  COMMENT "Building agnocast_heaphook (Rust shared library)"
)

install(FILES ${HEAPHOOK_OUTPUT}
  DESTINATION lib
)

ament_package()
