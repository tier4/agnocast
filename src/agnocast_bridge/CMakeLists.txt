cmake_minimum_required(VERSION 3.5)
project(agnocast_bridge)

find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(std_msgs REQUIRED)

find_package(agnocastlib REQUIRED)
find_package(sample_interfaces REQUIRED)
find_package(agnocast_heaphook REQUIRED)

add_executable(bridge_node src/bridge_node.cpp)
ament_target_dependencies(bridge_node rclcpp agnocast_heaphook agnocastlib sample_interfaces)
target_include_directories(bridge_node PRIVATE
  ${agnocast_heaphook_INCLUDE_DIRS}
  ${agnocastlib_INCLUDE_DIRS}
)

target_link_libraries(bridge_node
  agnocast_heaphook::preloaded
)

install(TARGETS
  bridge_node
  DESTINATION lib/${PROJECT_NAME}
)

install(DIRECTORY launch
  DESTINATION share/${PROJECT_NAME}/
)

ament_package()
