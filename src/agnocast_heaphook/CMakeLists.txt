cmake_minimum_required(VERSION 3.8)
project(agnocast_heaphook)

if(CMAKE_COMPILER_IS_GNUCXX OR CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  add_compile_options(-Wall -Wextra -Wpedantic)
endif()

find_package(ament_cmake REQUIRED)
find_package(tlsf REQUIRED)

if(BUILD_TESTING)
  find_package(ament_lint_auto REQUIRED)
  # the following line skips the linter which checks for copyrights
  # comment the line when a copyright and license is added to all source files
  set(ament_cmake_copyright_FOUND TRUE)
  # the following line skips cpplint (only works in a git repo)
  # comment the line when this package is in a git repo and when
  # a copyright and license is added to all source files
  set(ament_cmake_cpplint_FOUND TRUE)
  ament_lint_auto_find_test_dependencies()
endif()

include(CheckSymbolExists)
check_symbol_exists(mallinfo2 malloc.h HAVE_MALLINFO2)

add_library(preloaded SHARED src/preloaded.cpp)
target_link_libraries(preloaded PRIVATE tlsf::tlsf)
if(HAVE_MALLINFO2)
  target_compile_definitions(preloaded
    PRIVATE
      HAVE_MALLINFO2
  )
endif()

install(TARGETS preloaded DESTINATION lib)

ament_package()
