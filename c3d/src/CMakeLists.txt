# Plugin
# ------

add_library(C3dCore C3d.cpp)

add_llvm_library(C3d MODULE C3d.cpp PLUGIN_TOOL clang)

# Library order obtained by running VERBOSE=1 make in LLVM's build directory,
# then skimming the log to obtain the linker's invocation for
# libclang.$(SO)
if(APPLE)
  target_link_libraries(C3d PRIVATE
    clangAST
    clangBasic
    clangDriver
    clangFrontend
    clangIndex
    clangLex
    clangSema
    clangSerialization
    clangTooling
    clangARCMigrate
    LLVMX86CodeGen
    LLVMX86AsmParser
    LLVMX86Desc
    LLVMX86Disassembler
    LLVMX86Info
    LLVMCore
    LLVMSupport
    clangFormat
    clangToolingInclusions
    clangToolingCore
    clangFrontend
    clangDriver
    LLVMOption
    clangParse
    clangSerialization
    clangSema
    clangEdit
    clangRewrite
    clangAnalysis
    clangASTMatchers
    clangAST
    clangLex
    clangBasic
    LLVMFrontendOpenMP
    LLVMAsmPrinter
    LLVMDebugInfoDWARF
    LLVMCFGuard
    LLVMGlobalISel
    LLVMSelectionDAG
    LLVMCodeGen
    LLVMBitWriter
    LLVMScalarOpts
    LLVMAggressiveInstCombine
    LLVMInstCombine
    LLVMTransformUtils
    LLVMTarget
    LLVMAnalysis
    LLVMProfileData
    LLVMObject
    LLVMBitReader
    LLVMCore
    LLVMRemarks
    LLVMBitstreamReader
    LLVMTextAPI
    LLVMMCParser
    LLVMMCDisassembler
    LLVMMC
    LLVMBinaryFormat
    LLVMDebugInfoCodeView
    LLVMDebugInfoMSF
    LLVMSupport
    LLVMDemangle
  )
endif()
