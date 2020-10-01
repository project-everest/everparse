# Standalone
# ----------

include_directories(../src)

add_executable(clang-c3d
  main.cpp)

target_link_libraries(clang-c3d
  PRIVATE
  C3dCore
  ${CLANGLIBS}
)
