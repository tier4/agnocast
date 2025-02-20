cmake_minimum_required(VERSION 3.14)
project(agnocast_ioctl_wrapper)

find_package(ament_cmake REQUIRED)

add_library(agnocast_ioctl_wrapper SHARED src/topic_list.cpp)

install(TARGETS agnocast_ioctl_wrapper LIBRARY DESTINATION lib)

ament_package()
