#include "clang/Driver/Compilation.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/FileUtilities.h"
#include "llvm/Support/CommandLine.h"

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
    LLVM_DEBUG(llvm::dbgs() << "clang-c3d: start AST consumer\n");
    return std::make_unique<C3dASTConsumer>(&CI);
  }
};

// Option to specify a file name for a list of header files to check.
static cl::list<std::string>
    ListFileNames(cl::Positional, cl::value_desc("list"),
                  cl::desc("<list of one or more header list files>"),
                  cl::CommaSeparated);

static cl::opt<bool>
Debug("c3debug", cl::init(false),
cl::desc("Enabled c3d internal debugging"));


// Collect all other arguments, which will be passed to the front end.
static cl::list<std::string>
    CC1Arguments(cl::ConsumeAfter,
                 cl::desc("<arguments to be passed to front end>..."));

// Query apple's `xcrun` launcher, which is the source of truth for "how should"
// clang be invoked on this system.
llvm::Optional<std::string> queryXcrun(llvm::ArrayRef<llvm::StringRef> Argv) {
  auto Xcrun = llvm::sys::findProgramByName("xcrun");
  if (!Xcrun) {
    fprintf(stderr, "Couldn't find xcrun. Hopefully you have a non-apple toolchain...");
    return llvm::None;
  }
  llvm::SmallString<64> OutFile;
  llvm::sys::fs::createTemporaryFile("clangd-xcrun", "", OutFile);
  llvm::FileRemover OutRemover(OutFile);
  llvm::Optional<llvm::StringRef> Redirects[3] = {
      /*stdin=*/{""}, /*stdout=*/{OutFile}, /*stderr=*/{""}};
  // vlog("Invoking {0} to find clang installation", *Xcrun);
  int Ret = llvm::sys::ExecuteAndWait(*Xcrun, Argv,
                                      /*Env=*/llvm::None, Redirects,
                                      /*SecondsToWait=*/10);
  if (Ret != 0) {
    fprintf(stderr, "xcrun exists but failed with code %d. "
        "If you have a non-apple toolchain, this is OK. "
        "Otherwise, try xcode-select --install.",
        Ret);
    return llvm::None;
  }

  auto Buf = llvm::MemoryBuffer::getFile(OutFile);
  if (!Buf) {
    fprintf(stderr, "Can't read xcrun output: %s", Buf.getError().message().c_str());
    return llvm::None;
  }
  StringRef Path = Buf->get()->getBuffer().trim();
  if (Path.empty()) {
    fprintf(stderr, "xcrun produced no output");
    return llvm::None;
  }
  return Path.str();
}

int main(int Argc, const char *Argv[]) {
  // TODO: the following steps need to happen
  // ii) figure out how to load and enable plugins; apparently the plugin
  //     loading code does not kick in with our custom driver, but! we are
  //     linking in the plugin so it ought to do something (famous last words?)

  llvm::Optional<std::string> Path;
  SmallVector<const char *, 20> NewArgv;
  NewArgv.push_back(Argv[0]);
  for (int i = 1; i < Argc; ++i)
    NewArgv.push_back(Argv[i]);
  NewArgv.push_back("-std=c2x");
#ifdef __APPLE__
  Path = queryXcrun({"xcrun", "--show-sdk-path"});
  if (Path.hasValue()) {
    NewArgv.push_back("-isysroot");
    NewArgv.push_back(Path.getValue().c_str());
  }
#endif

  int NewArgc = static_cast<int>(NewArgv.size());
  cl::ParseCommandLineOptions(NewArgc, &NewArgv[0], "c3d.\n");

  // After this line, LLVM_DEBUG will start doing something!
  if (Debug.getValue()) {
    llvm::DebugFlag = true;
    setCurrentDebugType(DEBUG_TYPE);
  }

  // No go if we have no header list file.
  if (ListFileNames.size() == 0) {
    cl::PrintHelpMessage();
    return 1;
  }

  SmallString<256> PathBuf;
  sys::fs::current_path(PathBuf);
  std::unique_ptr<CompilationDatabase> Compilations;
  Compilations.reset(
      new FixedCompilationDatabase(Twine(PathBuf), CC1Arguments));

  // Compilations.getFileNames() doesn't work here.
  ClangTool Tool(*Compilations, ListFileNames);

  return Tool.run(newFrontendActionFactory<C3dFrontendAction>().get());
}
