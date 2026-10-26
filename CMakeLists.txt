cmake_minimum_required(VERSION 3.10)

project(bch_511_385_14 CXX)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release CACHE STRING "" FORCE)
endif()

add_library(bch STATIC src/m17_bch.cpp)
target_include_directories(bch PUBLIC src)

# Let CMake pick the optimisation level (Release is -O3 by default); just make
# sure the codec compiles cleanly with warnings on.
target_compile_options(bch PRIVATE -Wall -Wextra)

add_executable(m17_bch src/demo.cpp)
target_link_libraries(m17_bch PRIVATE bch)

enable_testing()

add_executable(test_bch tests/test_bch.cpp)
target_link_libraries(test_bch PRIVATE bch)
add_test(NAME bch_unit_tests COMMAND test_bch)
