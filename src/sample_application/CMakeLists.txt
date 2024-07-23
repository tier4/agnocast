cmake_minimum_required(VERSION 3.8)
project(sample_application)

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

# find dependencies
find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(std_msgs REQUIRED)

find_package(agnocastlib REQUIRED)
find_package(sample_interfaces REQUIRED)
find_package(agnocast_heaphook REQUIRED)

if(BUILD_TESTING)
  find_package(ament_lint_auto REQUIRED)
  # the following line skips the linter which checks for copyrights
  # uncomment the line when a copyright and license is not present in all source files
  #set(ament_cmake_copyright_FOUND TRUE)
  # the following line skips cpplint (only works in a git repo)
  # uncomment the line when this package is not in a git repo
  #set(ament_cmake_cpplint_FOUND TRUE)
  ament_lint_auto_find_test_dependencies()
endif()

add_executable(talker src/minimal_publisher.cpp)
ament_target_dependencies(talker rclcpp agnocast_heaphook agnocastlib sample_interfaces)
target_include_directories(talker PRIVATE
  ${agnocast_heaphook_INCLUDE_DIRS}
  ${agnocastlib_INCLUDE_DIRS}
)

target_link_libraries(talker
  agnocast_heaphook::preloaded
)

add_executable(listen_talker src/minimal_pubsub.cpp)
ament_target_dependencies(listen_talker rclcpp agnocast_heaphook agnocastlib sample_interfaces)
target_include_directories(listen_talker PRIVATE
  ${agnocast_heaphook_INCLUDE_DIRS}
  ${agnocastlib_INCLUDE_DIRS}
)

target_link_libraries(listen_talker
  agnocast_heaphook::preloaded
)

add_executable(listener src/minimal_subscriber.cpp)
ament_target_dependencies(listener rclcpp agnocast_heaphook agnocastlib sample_interfaces)
target_include_directories(listener PRIVATE
  ${agnocast_heaphook_INCLUDE_DIRS}
  ${agnocastlib_INCLUDE_DIRS}
)

target_link_libraries(listener
  agnocast_heaphook::preloaded
)

install(TARGETS talker listen_talker listener
  DESTINATION lib/${PROJECT_NAME})

install(DIRECTORY launch
  DESTINATION share/${PROJECT_NAME}/
)

ament_package()
