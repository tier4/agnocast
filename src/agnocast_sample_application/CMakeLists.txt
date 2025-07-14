cmake_minimum_required(VERSION 3.14)
project(agnocast_sample_application)

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

# find dependencies
find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(rclcpp_components REQUIRED)
find_package(std_msgs REQUIRED)

find_package(agnocastlib REQUIRED)
find_package(agnocast_sample_interfaces REQUIRED)

add_executable(talker src/minimal_publisher.cpp)
ament_target_dependencies(talker rclcpp agnocastlib agnocast_sample_interfaces)
target_include_directories(talker PRIVATE
  ${agnocastlib_INCLUDE_DIRS}
)

add_executable(listener src/minimal_subscriber.cpp)
ament_target_dependencies(listener rclcpp rclcpp_components std_msgs agnocastlib agnocast_sample_interfaces)
target_include_directories(listener PRIVATE
  ${agnocastlib_INCLUDE_DIRS}
)

install(TARGETS talker listener
  DESTINATION lib/${PROJECT_NAME})

install(DIRECTORY launch
  DESTINATION share/${PROJECT_NAME}/
)

ament_package()
