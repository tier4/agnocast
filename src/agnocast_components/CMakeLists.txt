cmake_minimum_required(VERSION 3.14)
project(agnocast_components)

find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(rclcpp_components REQUIRED)
find_package(class_loader REQUIRED)
find_package(agnocastlib REQUIRED)
find_package(cie_thread_configurator REQUIRED)
find_package(glog REQUIRED)

# agnocast_component_container (single-threaded)
add_executable(agnocast_component_container src/agnocast_component_container.cpp)
target_link_libraries(agnocast_component_container glog::glog)
ament_target_dependencies(agnocast_component_container rclcpp rclcpp_components agnocastlib)

# agnocast_component_container_mt (multi-threaded)
add_executable(agnocast_component_container_mt src/agnocast_component_container_mt.cpp)
target_link_libraries(agnocast_component_container_mt glog::glog)
ament_target_dependencies(agnocast_component_container_mt rclcpp rclcpp_components agnocastlib)

# agnocast_component_container_cie (callback-isolated executor)
add_executable(agnocast_component_container_cie src/agnocast_component_container_cie.cpp)
target_link_libraries(agnocast_component_container_cie glog::glog)
ament_target_dependencies(agnocast_component_container_cie rclcpp rclcpp_components agnocastlib cie_thread_configurator)

install(
  TARGETS agnocast_component_container agnocast_component_container_mt agnocast_component_container_cie
  DESTINATION lib/${PROJECT_NAME}
)

install(
  DIRECTORY cmake/
  DESTINATION share/${PROJECT_NAME}/cmake
)

install(
  FILES src/node_main.cpp.in src/node_main_agnocast_only.cpp.in
  DESTINATION share/${PROJECT_NAME}/src
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
