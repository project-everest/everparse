# General configuration
# ---------------------
#
# Some bits taken from https://github.com/nsumner/clang-plugins-demo/blob/master/CMakeLists.txt
# The overall idea is that LLVM provides some reusable CMake packages in its
# build directory, so we just need to include those and we get the benefits of
# all the proper definitions, etc.

project(c3d)
cmake_minimum_required(VERSION 3.17)

# TODO: couldn't find how to reuse the flags as picked by the build of LLVM
# itself
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -std=c++14 -fno-rtti -fno-omit-frame-pointer")

# Reusing the LLVM CMake stuff
# ----------------------------
#
# Note: we expect users to invoke cmake -DLLVM_BUILD_DIR=path/to/llvm-project/out

set(CLANG_DIR "${LLVM_BUILD_ROOT}/lib/cmake/clang")
set(LLVM_DIR "${LLVM_BUILD_ROOT}/lib/cmake/llvm")

list(APPEND CMAKE_MODULE_PATH "${LLVM_DIR}")
list(APPEND CMAKE_MODULE_PATH "${CLANG_DIR}")

find_package(LLVM REQUIRED CONFIG HINTS ${LLVM_DIR})
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

find_package(Clang REQUIRED CONFIG HINTS ${CLANG_DIR})
message(STATUS "Using Clang.cmake in: ${CLANG_DIR}")

# Relies on properly appending the LLVM_DIR to CMAKE_MODULE_PATH!
include(AddLLVM)

message("LLVM STATUS:
  Definitions ${LLVM_DEFINITIONS}
  Includes    ${LLVM_INCLUDE_DIRS}
              ${CLANG_INCLUDE_DIRS}
  Libraries   ${LLVM_LIBRARY_DIRS}")

include_directories(SYSTEM ${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})
add_definitions(${LLVM_DEFINITIONS})

# Actual project
# --------------

add_llvm_library(C3d MODULE C3d.cpp PLUGIN_TOOL clang)

set(LLVM_LINK_COMPONENTS Support)
set(CMAKE_EXPORT_COMPILE_COMMANDS true)
target_link_libraries(C3d PRIVATE
  clang
  LLVMSupport
)
