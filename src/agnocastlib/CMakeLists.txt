cmake_minimum_required(VERSION 3.8)
project(agnocastlib)

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

# find dependencies
find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)

add_library(agnocast SHARED src/agnocast.cpp src/agnocast_publisher.cpp src/agnocast_smart_pointer.cpp)
# ament_target_dependencies(agnocast rclcpp)

target_link_libraries(agnocast
  ${rclcpp_LIBRARIES}
)

target_include_directories(agnocast PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include>
  ${rclcpp_INCLUDE_DIRS}
)

install(TARGETS agnocast
  EXPORT export_${PROJECT_NAME}
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
  RUNTIME DESTINATION bin
  INCLUDES DESTINATION include
)

install(
  DIRECTORY include/
  DESTINATION include
)

install(TARGETS agnocast DESTINATION lib/${PROJECT_NAME})

ament_export_targets(export_${PROJECT_NAME} HAS_LIBRARY_TARGET)
ament_export_include_directories(include)
ament_package()
