cmake_minimum_required(VERSION 3.14)
project(agnocast_components)

find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(rclcpp_components REQUIRED)
find_package(class_loader REQUIRED)
find_package(agnocastlib REQUIRED)

# Install cmake modules
install(
  DIRECTORY cmake/
  DESTINATION share/${PROJECT_NAME}/cmake
)

# Install node_main.cpp.in templates
install(
  FILES node_main.cpp.in node_main_agnocast_only.cpp.in
  DESTINATION share/${PROJECT_NAME}
)

ament_export_dependencies(
  rclcpp
  rclcpp_components
  class_loader
  agnocastlib
)

ament_package(
  CONFIG_EXTRAS
    "agnocast_components-extras.cmake.in"
)
