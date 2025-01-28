cmake_minimum_required(VERSION 3.14)
project(e2e_test)

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

# find dependencies
find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(std_msgs REQUIRED)
find_package(agnocastlib REQUIRED)
find_package(launch_testing_ament_cmake REQUIRED)

add_executable(test_talker src/test_publisher.cpp)
ament_target_dependencies(test_talker rclcpp std_msgs agnocastlib)
target_include_directories(test_talker PRIVATE
  ${agnocastlib_INCLUDE_DIRS}
)

add_executable(test_listener src/test_subscriber.cpp)
ament_target_dependencies(test_listener rclcpp std_msgs agnocastlib)
target_include_directories(test_listener PRIVATE
  ${agnocastlib_INCLUDE_DIRS}
)

add_executable(test_taker src/test_take_subscriber.cpp)
ament_target_dependencies(test_taker rclcpp std_msgs agnocastlib)
target_include_directories(test_taker PRIVATE
  ${agnocastlib_INCLUDE_DIRS}
)

add_executable(test_ros2_listener src/test_ros2_subscriber.cpp)
ament_target_dependencies(test_ros2_listener rclcpp std_msgs)

install(TARGETS test_talker test_listener test_taker test_ros2_listener
  DESTINATION lib/${PROJECT_NAME})

install(DIRECTORY test
  DESTINATION share/${PROJECT_NAME}/
)

ament_package()
