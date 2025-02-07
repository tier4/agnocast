cmake_minimum_required(VERSION 3.14)
project(sample_application)

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

# find dependencies
find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(rclcpp_components REQUIRED)
find_package(std_msgs REQUIRED)

find_package(agnocastlib REQUIRED)
find_package(sample_interfaces REQUIRED)

add_executable(talker src/minimal_publisher.cpp)
ament_target_dependencies(talker rclcpp agnocastlib sample_interfaces)
target_include_directories(talker PRIVATE
  ${agnocastlib_INCLUDE_DIRS}
)

add_library(listener_component SHARED src/minimal_subscriber.cpp)
ament_target_dependencies(listener_component rclcpp rclcpp_components agnocastlib sample_interfaces)
target_include_directories(listener_component PRIVATE ${agnocastlib_INCLUDE_DIRS})

rclcpp_components_register_node(
  listener_component
  PLUGIN "MinimalSubscriber"
  EXECUTABLE listener
)

add_executable(callback_group_test_talker src/callback_group_test_talker.cpp)
ament_target_dependencies(callback_group_test_talker rclcpp agnocastlib)
target_include_directories(callback_group_test_talker PRIVATE
  ${agnocastlib_INCLUDE_DIRS}
)

add_library(callback_group_test_listener_component SHARED src/callback_group_test_listener.cpp)
ament_target_dependencies(callback_group_test_listener_component rclcpp rclcpp_components agnocastlib)
target_include_directories(callback_group_test_listener_component PRIVATE ${agnocastlib_INCLUDE_DIRS})

rclcpp_components_register_node(
  callback_group_test_listener_component
  PLUGIN "CallbackGroupTestListener"
  EXECUTABLE callback_group_test_listener
)

ament_export_targets(export_listener_component)
install(TARGETS listener_component
        EXPORT export_listener_component
        ARCHIVE DESTINATION lib
        LIBRARY DESTINATION lib
        RUNTIME DESTINATION bin
)

ament_export_targets(export_callback_group_test_listener_component)
install(TARGETS callback_group_test_listener_component
        EXPORT export_callback_group_test_listener_component
        ARCHIVE DESTINATION lib
        LIBRARY DESTINATION lib
        RUNTIME DESTINATION bin
)

install(TARGETS talker callback_group_test_talker callback_group_test_listener
  DESTINATION lib/${PROJECT_NAME})

install(DIRECTORY launch
  DESTINATION share/${PROJECT_NAME}/
)

ament_package()
