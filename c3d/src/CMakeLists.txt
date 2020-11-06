# Static library
# --------------
#
# To be linked into the main executable. My understanding of the
# -fvisibility=hidden flag is that it makes sure that C++ templates inlining do
# not generate symbol clashes when linking to the main clang libraries.

add_library(C3dCore C3d.cpp)
set_target_properties(C3dCore PROPERTIES CXX_VISIBILITY_PRESET hidden)

# Plugin
# ------

add_llvm_library(C3d MODULE C3d.cpp PLUGIN_TOOL clang)
set_target_properties(C3d PROPERTIES CXX_VISIBILITY_PRESET hidden)

# Library order obtained by running VERBOSE=1 make in LLVM's build directory,
# then skimming the log to obtain the linker's invocation for
# libclang.$(SO)
target_link_libraries(C3d PRIVATE
  ${CLANGLIBS}
)
