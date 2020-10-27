#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "llvm/Support/Debug.h"
#include <llvm/Support/CommandLine.h>

#include "C3d.h"

#define DEBUG_TYPE "c3d"

using namespace llvm;
using namespace clang;
using namespace clang::tooling;
using namespace c3d;

// A driver for compiling c3d as a standalone tool; good context at
// https://github.com/eliben/llvm-clang-samples/blob/master/src_clang/tooling_sample.cpp
// Better context at: clang-tools-extra/modularize/Modularize.cpp
class C3dFrontendAction : public ASTFrontendAction {
public:
  C3dFrontendAction() {}

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef file) override {
    return std::make_unique<C3dASTConsumer>(&CI);
  }
};

int main(int argc, const char **argv) {
  // TODO: the following steps need to happen
  // i) figure out how to pass suitable options to the compiler invocations,
  //    e.g. how to pass -std=c2x, how to pass a proper -include, etc.
  // ii) figure out how to load and enable plugins; apparently the plugin
  //     loading code does not kick in with our custom driver, but! we are
  //     linking in the plugin so it ought to do something (famous last words?)

  // Build a modified command-line where the arguments below have been prepended
  // to the invocation.
  int MyArgc = argc + 3;
  const char *MyArgv[MyArgc];
  MyArgv[0] = argv[0];
  MyArgv[1] = "-std=c2x";
  MyArgv[2] = "-mllvm";
  MyArgv[3] = "-debug-only=c3d";
  memcpy(MyArgv+4, argv+1, (argc - 1)*sizeof(char *));

  cl::ParseCommandLineOptions(MyArgc, MyArgv, "c3d.\n");


  /* for (int i = 0; i < MyArgc; ++i) */
  /*   printf("%s ", MyArgv[i]); */
  /* printf("\n"); */
  std::string ErrorMsg;
  std::unique_ptr<CompilationDatabase> MyCD;
  MyCD.reset(
    FixedCompilationDatabase::loadFromCommandLine(MyArgc, MyArgv, ErrorMsg));
  if (MyCD == nullptr) {
    fprintf(stderr, "Error parsing the command-line:\n%s\n", ErrorMsg.c_str());
    exit(1);
  }

  printf("all compile commands (%d):\n", MyArgc);
  for (auto &CC: MyCD->getAllCompileCommands()) {
    printf("invocation: ");
    for (const auto &s: CC.CommandLine)
      printf("%s ", s.c_str());
    printf("\n");
  }

  // TODO: OP.getCompilations() is useless as it attempts to read from some
  // CompileCommands!
  ClangTool Tool(*MyCD, MyCD->getAllFiles());

  // ClangTool::run accepts a FrontendActionFactory, which is then used to
  // create new objects implementing the FrontendAction interface. Here we use
  // the helper newFrontendActionFactory to create a default factory that will
  // return a new MyFrontendAction object every time.
  // To further customize this, we could create our own factory class.
  return Tool.run(newFrontendActionFactory<C3dFrontendAction>().get());
}
