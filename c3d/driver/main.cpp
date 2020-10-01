#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"

#include "C3d.h"

using namespace clang;
using namespace clang::tooling;
using namespace c3d;

// A driver for compiling c3d as a standalone tool; good context at
// https://github.com/eliben/llvm-clang-samples/blob/master/src_clang/tooling_sample.cpp
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
  CommonOptionsParser op(argc, argv, llvm::cl::GeneralCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  // ClangTool::run accepts a FrontendActionFactory, which is then used to
  // create new objects implementing the FrontendAction interface. Here we use
  // the helper newFrontendActionFactory to create a default factory that will
  // return a new MyFrontendAction object every time.
  // To further customize this, we could create our own factory class.
  return Tool.run(newFrontendActionFactory<C3dFrontendAction>().get());
}
