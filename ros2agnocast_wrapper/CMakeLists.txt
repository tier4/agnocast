cmake_minimum_required(VERSION 3.14)
project(ros2agnocast_wrapper)

find_package(ament_cmake REQUIRED)

add_library(ros2agnocast_wrapper SHARED ros2agnocast_wrapper.c)

install(TARGETS ros2agnocast_wrapper LIBRARY DESTINATION lib)

ament_package()
