cmake_minimum_required(VERSION 3.14)
project(agnocastlib)

# Clang requires explicit C++ standard setting to find standard library headers
if(NOT CMAKE_CXX_STANDARD)
  set(CMAKE_CXX_STANDARD 17)
endif()

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
find_package(tracetools REQUIRED)
find_package(LTTngUST REQUIRED)
find_package(Python3 REQUIRED)

add_library(agnocast SHARED
  src/agnocast.cpp src/agnocast_utils.cpp src/agnocast_publisher.cpp src/agnocast_subscription.cpp
  src/agnocast_smart_pointer.cpp src/agnocast_callback_info.cpp src/agnocast_executor.cpp
  src/agnocast_single_threaded_executor.cpp src/agnocast_multi_threaded_executor.cpp
  src/agnocast_callback_isolated_executor.cpp src/agnocast_tracepoint_wrapper.c)
# ament_target_dependencies(agnocast rclcpp)

target_link_libraries(agnocast
  ${rclcpp_LIBRARIES}
  ${tracetools_LIBRARIES}
  ${LTTNGUST_LIBRARIES}
)

target_include_directories(agnocast PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include>
  ${rclcpp_INCLUDE_DIRS}
  ${tracetools_INCLUDE_DIRS}
  ${LTTNGUST_INCLUDE_DIRS}
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

### ▼▼▼ Start of generic bridge daemon configuration ▼▼▼

# 1. Generate a file specifying the list of messages to be built
set(MESSAGE_TYPES_FILE "${CMAKE_CURRENT_BINARY_DIR}/ros2_interfaces.txt")
execute_process(
  COMMAND ros2 interface list -m
  OUTPUT_FILE "${MESSAGE_TYPES_FILE}"
  RESULT_VARIABLE ros2_list_res
  OUTPUT_STRIP_TRAILING_WHITESPACE
)

if(NOT ros2_list_res EQUAL 0)
  message(FATAL_ERROR "Failed to execute 'ros2 interface list -m'. Is ROS2 sourced correctly?")
endif()

if(NOT EXISTS "${MESSAGE_TYPES_FILE}")
  message(FATAL_ERROR "Temporary message list file not found: ${MESSAGE_TYPES_FILE}")
endif()

# 2. Generate C++ code and a dependency list using a Python script
set(GENERATED_TYPES_DIR "${CMAKE_CURRENT_BINARY_DIR}/generated_bridge_types")
set(GENERATED_DEPENDENCIES_TXT "${CMAKE_CURRENT_BINARY_DIR}/generated_dependencies.txt")
set(REGISTRATION_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/scripts/generate_registrations.py")

execute_process(
  COMMAND ${Python3_EXECUTABLE} "${REGISTRATION_SCRIPT}"
          "${MESSAGE_TYPES_FILE}"
          "${GENERATED_TYPES_DIR}"
          "${GENERATED_DEPENDENCIES_TXT}"
  RESULT_VARIABLE script_res
)
if(NOT script_res EQUAL 0)
  message(FATAL_ERROR "Python script for code generation failed with exit code ${script_res}")
endif()

# 3. Read the generated dependency list
file(STRINGS "${GENERATED_DEPENDENCIES_TXT}" auto_dependencies)
file(GLOB GENERATED_REGISTRATION_FILES "${GENERATED_TYPES_DIR}/*.cpp")

# 4. Add the generic bridge daemon executable
add_executable(agnocast_ros2_to_agnocast_bridge_daemon
  src/agnocast_ros2_to_agnocast_bridge_daemon.cpp
  ${GENERATED_REGISTRATION_FILES}
)

# 5. Set include directories for this target itself
target_include_directories(agnocast_ros2_to_agnocast_bridge_daemon PRIVATE
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
  $<INSTALL_INTERFACE:include>
  ${agnocast_sample_interfaces_INCLUDE_DIRS}
)

# 6. Process all found dependencies
foreach(dep ${auto_dependencies})
  find_package(${dep} REQUIRED)
  target_include_directories(agnocast_ros2_to_agnocast_bridge_daemon PRIVATE
    ${${dep}_INCLUDE_DIRS}
  )
endforeach()

# 7. Set linked libraries and ament dependencies
target_link_libraries(agnocast_ros2_to_agnocast_bridge_daemon agnocast)
ament_target_dependencies(agnocast_ros2_to_agnocast_bridge_daemon
  rclcpp
  ${auto_dependencies}
)

# 8. Trigger CMake reconfiguration if critical files change.
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS
  "${MESSAGE_TYPES_FILE}"
  "${REGISTRATION_SCRIPT}"
)

### ▲▲▲ End of generic bridge daemon configuration ▲▲▲

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

install(
  TARGETS agnocast_ros2_to_agnocast_bridge_daemon
  DESTINATION lib/${PROJECT_NAME}
)

execute_process(
  COMMAND ${Python3_EXECUTABLE} -c "import xml.etree.ElementTree as ET; print(ET.parse('${CMAKE_CURRENT_SOURCE_DIR}/package.xml').getroot().find('version').text)"
  OUTPUT_VARIABLE PACKAGE_VERSION
  OUTPUT_STRIP_TRAILING_WHITESPACE
)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/include/agnocast/agnocast_version.hpp.in
  ${CMAKE_CURRENT_BINARY_DIR}/include/agnocast/agnocast_version.hpp
)

include_directories(${CMAKE_CURRENT_BINARY_DIR}/include)

if(BUILD_TESTING)
  find_package(ament_cmake_gmock REQUIRED)
  
  # Unit tests
  ament_add_gmock(test_unit_${PROJECT_NAME}
    test/unit/test_agnocast_utils.cpp
    test/unit/test_agnocast_subscription.cpp
    test/unit/test_mocked_agnocast.cpp
    test/unit/test_agnocast_executors.cpp)
  target_include_directories(test_unit_${PROJECT_NAME} PRIVATE include)
  target_link_libraries(test_unit_${PROJECT_NAME} agnocast)
  set_tests_properties(test_unit_${PROJECT_NAME} PROPERTIES
    ENVIRONMENT "GTEST_DEATH_TEST_STYLE=threadsafe"
  )

  # Integration tests
  ament_add_gmock(test_integration_${PROJECT_NAME}
    test/integration/test_agnocast_single_threaded_executor.cpp
    test/integration/test_agnocast_multi_threaded_executor.cpp
    test/integration/src/ioctl_mock.cpp
    test/integration/src/node_for_executor_test.cpp)
  target_include_directories(test_integration_${PROJECT_NAME} PRIVATE test/integration/include)
  target_link_libraries(test_integration_${PROJECT_NAME} agnocast)
  set_tests_properties(test_integration_${PROJECT_NAME} PROPERTIES
    ENVIRONMENT "GTEST_DEATH_TEST_STYLE=threadsafe"
    TIMEOUT 120
  )

  # Integration tests for agnocast_heaphook
  add_library(initialize_shutdown_mock SHARED test/integration/src/initialize_shutdown_mock.cpp)
  set_target_properties(initialize_shutdown_mock PROPERTIES
      OUTPUT_NAME "initialize_shutdown_mock"
      LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib
  )
  install(TARGETS initialize_shutdown_mock
      LIBRARY DESTINATION lib
  )

  ament_add_gmock(test_integration_agnocast_heaphook
    test/integration/test_agnocast_heaphook.cpp)
  target_link_libraries(test_integration_agnocast_heaphook agnocast)
  set_tests_properties(test_integration_agnocast_heaphook PROPERTIES
    ENVIRONMENT "GTEST_DEATH_TEST_STYLE=threadsafe;LD_PRELOAD=${CMAKE_INSTALL_PREFIX}/lib/libinitialize_shutdown_mock.so:${CMAKE_INSTALL_PREFIX}/lib/libagnocast_heaphook.so:;AGNOCAST_MEMPOOL_SIZE=1000000")
endif()

ament_export_targets(export_${PROJECT_NAME} HAS_LIBRARY_TARGET)
ament_export_include_directories(include)
ament_package()
