# Standalone
# ----------

include_directories(../src)

add_executable(clang-c3d
  main.cpp)

target_link_libraries(clang-c3d
  PUBLIC
  C3dCore
  clangTooling
  LLVMSupport
)
