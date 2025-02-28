cmake_minimum_required(VERSION 3.14)
project(agnocast_kmod)

find_package(ament_cmake REQUIRED)

set(KMOD_SRC_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set(KMOD_OUTPUT ${KMOD_SRC_DIR}/agnocast.ko)

add_custom_target(build_agnocast_kmod ALL
  COMMAND make -C ${KMOD_SRC_DIR}
  BYPRODUCTS ${KMOD_OUTPUT}
  WORKING_DIRECTORY ${KMOD_SRC_DIR}
  COMMENT "Building agnocast kernel module"
)

# Install the module inside colcon install directory instead of system directories
install(FILES ${KMOD_OUTPUT}
  DESTINATION share/${PROJECT_NAME}
)

ament_package()
