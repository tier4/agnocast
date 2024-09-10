cmake_minimum_required(VERSION 3.8)
project(agnocast_heaphook)

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

find_package(ament_cmake REQUIRED)
find_package(tlsf REQUIRED)
find_package(rclcpp REQUIRED)
find_package(agnocastlib REQUIRED)

include_directories(include)

add_library(util src/util.cpp)

if(BUILD_TESTING)
  find_package(ament_cmake_gtest REQUIRED)
  ament_add_gtest(${PROJECT_NAME}_test test/test_util.cpp)
  target_include_directories(${PROJECT_NAME}_test PUBLIC include)
  target_link_libraries(${PROJECT_NAME}_test util)
endif()

include(CheckSymbolExists)
check_symbol_exists(mallinfo2 malloc.h HAVE_MALLINFO2)

add_library(preloaded SHARED src/preloaded.cpp)
target_link_libraries(preloaded PRIVATE agnocastlib::agnocast tlsf::tlsf util ${rclcpp_LIBRARIES})
if(HAVE_MALLINFO2)
  target_compile_definitions(preloaded
    PRIVATE
      HAVE_MALLINFO2
  )
endif()

install(TARGETS preloaded DESTINATION lib)

ament_package()
