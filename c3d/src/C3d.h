//===- C3d.h --------------------------------------------------------------===//
//
// c3d is a clang plugin that parses everparse annotations as C2x attributes and
// generates corresponding .3d files, along with a header file stripped of the
// everparse attributes, which enables further processing by a
// non-C2x-attributes aware tool.
//
// In order to use c3d, invoke clang with -std=c2x
// -fplugin=path/to/thisplugin.{so,dll,dylib}
//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/CompilerInstance.h"

using namespace clang;

namespace c3d {

class C3dASTConsumer : public ASTConsumer {
private:
  CompilerInstance *CI;

public:
  explicit C3dASTConsumer(CompilerInstance *CI_)
    : CI(CI_)
    { }

  void HandleTranslationUnit(ASTContext &Context) override;
};

}
