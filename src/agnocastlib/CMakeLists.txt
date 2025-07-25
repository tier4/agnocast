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
find_package(tracetools REQUIRED)
find_package(LTTngUST REQUIRED)

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

find_package(Python3 REQUIRED)

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
