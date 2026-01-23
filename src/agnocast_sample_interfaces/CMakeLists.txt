cmake_minimum_required(VERSION 3.14)
project(agnocast_sample_interfaces)

# Skip building and installation if in Jazzy environment
# TODO(mitsudome-r): Remove this workaround when Jazzy supports agnocast
if("$ENV{ROS_DISTRO}" STREQUAL "jazzy")
  message(WARN "Skipping ${PROJECT_NAME} build in Jazzy environment")
  find_package(ament_cmake REQUIRED)
  ament_package()
  return()
endif()

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

# find dependencies
find_package(ament_cmake REQUIRED)
find_package(rosidl_default_generators REQUIRED)

rosidl_generate_interfaces(${PROJECT_NAME}
  "msg/DynamicSizeArray.msg"
  "msg/StaticSizeArray.msg"
  "srv/SumIntArray.srv"
)

ament_package()
