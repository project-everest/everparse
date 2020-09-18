# Plugin
# ------

add_library(C3dCore C3d.cpp)

add_llvm_library(C3d MODULE C3d.cpp PLUGIN_TOOL clang)

# TODO: I don't understand why, but this causes a segfault on Linux where some
# global initializer seems to be called twice; try switching PRIVATE for PUBLIC?
if(APPLE)
  target_link_libraries(C3d PRIVATE
    clang
    LLVMSupport
  )
endif()
