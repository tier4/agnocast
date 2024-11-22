cmake_minimum_required(VERSION 3.14)
project(agnocastlib)

option(COVERAGE "Enable coverage reporting for gcov" OFF)

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
  if(COVERAGE)
    add_compile_options(--coverage -g)
    add_link_options(--coverage)
  endif()
endif()

# find dependencies
find_package(ament_cmake REQUIRED)
find_package(rclcpp REQUIRED)
find_package(rclcpp_components REQUIRED)

add_library(agnocast SHARED
  src/agnocast.cpp src/agnocast_utils.cpp src/agnocast_publisher.cpp src/agnocast_subscription.cpp
  src/agnocast_smart_pointer.cpp src/agnocast_topic_info.cpp src/agnocast_executor.cpp
  src/agnocast_single_threaded_executor.cpp src/agnocast_multi_threaded_executor.cpp)
# ament_target_dependencies(agnocast rclcpp)

target_link_libraries(agnocast
  ${rclcpp_LIBRARIES}
)

target_include_directories(agnocast PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include>
  ${rclcpp_INCLUDE_DIRS}
)

add_executable(agnocast_component_container src/agnocast_component_container.cpp)

target_link_libraries(agnocast_component_container
  agnocast
)

ament_target_dependencies(agnocast_component_container rclcpp rclcpp_components)

add_executable(agnocast_component_container_mt src/agnocast_component_container_mt.cpp)

target_link_libraries(agnocast_component_container_mt
  agnocast
)

ament_target_dependencies(agnocast_component_container_mt rclcpp rclcpp_components)

install(
  TARGETS agnocast_component_container agnocast_component_container_mt
  DESTINATION lib/${PROJECT_NAME}
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

if(BUILD_TESTING)
  # For gmock-global
  include(FetchContent)
  FetchContent_Declare(
    gmock-global
    GIT_REPOSITORY https://github.com/apriorit/gmock-global.git
    GIT_TAG        master
  )
  FetchContent_MakeAvailable(gmock-global)
  include_directories(${gmock-global_SOURCE_DIR}/include)

  find_package(ament_cmake_gmock REQUIRED)
  ament_add_gmock(test_${PROJECT_NAME} test/test_agnocast_utils.cpp 
    test/test_agnocast_topic_info.cpp test/test_agnocast_subscription.cpp
    test/test_agnocast_smart_pointer.cpp)
  target_include_directories(test_${PROJECT_NAME} PRIVATE include)
  target_link_libraries(test_${PROJECT_NAME} gmock-global agnocast)
  set_tests_properties(test_${PROJECT_NAME} PROPERTIES
    ENVIRONMENT "GTEST_DEATH_TEST_STYLE=threadsafe"
  )
endif()

ament_export_targets(export_${PROJECT_NAME} HAS_LIBRARY_TARGET)
ament_export_include_directories(include)
ament_package()
