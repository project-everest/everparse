//===- C3d.cpp ------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
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

#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/Basic/DiagnosticSema.h"
#include "clang/Basic/FileManager.h"
#include "clang/Parse/Parser.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/ParsedAttr.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/Scope.h"
#include "clang/Sema/SemaDiagnostic.h"
#include "llvm/IR/Attributes.h"
#include "llvm/Support/Debug.h"
#include "clang/Basic/TokenKinds.h"

// We use the LLVM debug infrastructure -- see
// http://llvm.org/docs/ProgrammersManual.html#the-llvm-debug-macro-and-debug-option
// for detailed explanations. Notably, in order to see the debug output, you
// need to pass -mllvm -debug-only=c3d to the compiler driver (i.e. clang).
#define DEBUG_TYPE "c3d"

using namespace clang;

// C3d is made up of several clang plugins. The first one recognizes attributes
// (only in C2x mode for now, so you MUST pass -std=c2x), bails if they're used
// improperly, and records them internally in clang's AST as annotate nodes to
// be processed by later phases.
//
// Note that this is largely inspired by
// https://clang.llvm.org/docs/ClangPlugins.html#defining-attributes

namespace {

// TODO (general things):
// - settle on {} vs () for constructors (just be consistent)
// - run the file through clang-format

// A helper class shared by multiple attributes; enforces that the attribute
// that has ``spelling`` only appears on top-level struct type declarations.
class C3dDiagOnStruct {
protected:
  const char *SpellingStr;

  explicit C3dDiagOnStruct(const char *SpellingStr): SpellingStr(SpellingStr) {}

  virtual bool diagAppertainsToDecl(Sema &S, const ParsedAttr &Attr,
                            const Decl *D) const {
    // TODO: provide a suggestion if the attribute is on the typedef, as it'll
    // be a common syntax error -- this is done somewhere in the clang source
    // code
    if (!isa<RecordDecl>(D)) {
      S.Diag(Attr.getLoc(), diag::warn_attribute_wrong_decl_type_str)
        << Attr << "struct declarations";
      return false;
    }
    LLVM_DEBUG(llvm::dbgs() << "c3d: found attribute " << SpellingStr << "\n");
    return true;
  }
};

// A helper class shared everywhere: deals with the boilerplate of setting up
// the spelling. Derived classes should inherit this instead of ParsedAttrInfo.
class C3dSimpleSpelling: public ParsedAttrInfo {
private:
  Spelling S[1];

public:
  C3dSimpleSpelling(const char *SpellingStr)
  {
    S[0] = Spelling { ParsedAttr::AS_C2x, SpellingStr };
    Spellings = S;
    LLVM_DEBUG(llvm::dbgs() << "c3d plugin for attribute " << SpellingStr << " loaded\n");
  }
};


// A general class for an attribute with no arguments that goes onto a struct
// type declaration. See tests/basic0.h for proper placement of this attribute.
class TrivialC3dAttrInfo : public C3dSimpleSpelling, C3dDiagOnStruct {
private:
  const char *InternalName;

public:
  TrivialC3dAttrInfo(const char *SpellingStr, const char *InternalName)
    : C3dSimpleSpelling{SpellingStr},
      C3dDiagOnStruct{SpellingStr},
      InternalName{InternalName}
  {
  }

  AttrHandling handleDeclAttribute(Sema &S, Decl *D,
                                   const ParsedAttr &Attr) const override {
    // Check if the decl is at file scope.
    // TODO: accept things that are within a C++ namespace so that we can work
    // in C++ mode.
    // TODO: move this into diagAppertainsToDecl for better error reporting? the
    // original Attribute plugin did this check here so I'm unsure.
    if (!D->getDeclContext()->isFileContext()) {
      unsigned ID = S.getDiagnostics().getCustomDiagID(
          DiagnosticsEngine::Error,
          "%0 attribute only allowed at file scope");
      S.Diag(Attr.getLoc(), ID) << SpellingStr;
      return AttributeNotApplied;
    }

    // Attach an annotate attribute to the Decl.
    D->addAttr(AnnotateAttr::Create(S.Context, InternalName, Attr.getRange()));
    return AttributeApplied;
  }
};

struct C3dProcessAttrInfo: TrivialC3dAttrInfo {
  C3dProcessAttrInfo(): TrivialC3dAttrInfo{"everparse::process", "c3d_process"} {
  }
};

struct C3dEntryPointAttrInfo: TrivialC3dAttrInfo {
  C3dEntryPointAttrInfo(): TrivialC3dAttrInfo{"everparse::entrypoint", "c3d_entrypoint"} {
  }
};

// When doing custom parsing, consuming everything until the next right paren
// mimics the behavior of the parser, and provide better parser recovery so
// that the rest of the declaration can be parsed properly.
ParsedAttrInfo::AttrHandling consumeUntilClosingParenAndError(Parser *P) {
  P->SkipUntil(tok::r_paren);
  return ParsedAttrInfo::AttributeNotApplied;
}

// This one recognizes the everparse::constraint attribute, validates it,
// renders it as a string and leaves that as a (built-in) annotate attribute to
// be caught later by the printer/rewriter.
//
// Note that ideally, we would have a custom attribute that can hold an
// expression, to be pretty-printed later in the "semantic" phase. The "right"
// way to achieve this would be to extend Attr.td in clang to allow for an
// attribute that holds a user-provided payload. (Suggestion by Aaron Ballman).
// This would require some non-trivial feature work in clang itself, as I have
// found no way to extend Attr.td with an out-of-tree plugin.
class C3dConstraintAttrInfo : public C3dSimpleSpelling {
public:
  C3dConstraintAttrInfo(): C3dSimpleSpelling("everparse::constraint") {
    NumArgs = 1;
  }

  bool diagAppertainsToDecl(Sema &S, const ParsedAttr &Attr,
                            const Decl *D) const override {
    if (!isa<FieldDecl>(D)) {
      S.Diag(Attr.getLoc(), diag::warn_attribute_wrong_decl_type_str)
        << Attr << "struct field declarations";
      return false;
    }
    // TODO: check isa<RecordDecl>(D->getParent()), then check the parent has
    // everparse::process
    //

    LLVM_DEBUG(llvm::dbgs() << "c3d: found attribute everparse::constraint\n");
    return true;
  }

  AttrHandling parseAttributePayload(Parser *P,
                                     ParsedAttributes &Attrs,
                                     Declarator *D,
                                     IdentifierInfo *AttrName,
                                     SourceLocation AttrNameLoc,
                                     SourceLocation *EndLoc,
                                     IdentifierInfo *ScopeName,
                                     SourceLocation ScopeLoc) const override {
    // Note: we don't have access to the internal API of the Parser here, which
    // makes things somewhat difficult. For instance, we don't have access to
    // ConsumeParen(), or ExpectAndConsume()...
    LLVM_DEBUG(llvm::dbgs() << "c3d: parsing argument to everparse::constraint\n");

    // Defer to the parser to produce a good error message.
    if (P->getCurToken().getKind() != tok::l_paren)
      return AttributeNotApplied;

    // Eat opening left parenthesis. Note: it's important to go through
    // ConsumeAnyToken, since it'll properly redirect into the
    // parenthesis-handling, internal parser code that increments the open
    // parenthesis count.
    P->ConsumeAnyToken();

    // This means we are not attached to the right kind of declaration. Provide
    // a meaningful error now.
    if (D == nullptr) {
      P->getActions().Diag(AttrNameLoc, diag::warn_attribute_wrong_decl_type_str)
        << "everparse::constraint" << "struct field declarations";
      return consumeUntilClosingParenAndError(P);
    }

    // Extend the scope so that we don't have resolution errors. We fake a
    // variable declaration just so that the name resolution is happy, and then
    // assume that the current context will be dropped anyhow.
    LLVM_DEBUG(llvm::dbgs() << "c3d: scope extension! " << D->getIdentifier()->getNameStart() << "\n");

    // Check if we are accumulating another constraint on the same field, in
    // which case no need to add this field to the scope
    // TODO: this did not work out. Why?
    // LookupResult LR(P->getActions(), D->getIdentifier(), D->getBeginLoc(), Sema::LookupAnyName);
    // if (LR.getResultKind() != LookupResult::Found) { ... }
    Sema &S = P->getActions();
    bool InScope = false;
    // TODO: figure out how to use specific_decl_iterator
    // TODO: not all declarations have names
    for (const auto &Decl: S.getCurScope()->decls())
      if (const auto *VD = dyn_cast<VarDecl>(Decl))
        if (VD->getName() == D->getIdentifier()->getName())
          InScope = true;

    if (!InScope) {
      TypeSourceInfo *T = S.GetTypeForDeclarator(*D, P->getCurScope());
      QualType R = T->getType();
      VarDecl *VD = VarDecl::Create(S.getASTContext(), S.CurContext,
          D->getBeginLoc(), D->getIdentifierLoc(), D->getIdentifier(), R,
          T,
          SC_None);
      VD->setImplicit(true);
      // Doing this makes sure Sema is aware of the new scope entry, meaning this name
      // will be in scope when parsing the expression. (Parsing and scope
      // resolution are intertwined.)
      S.PushOnScopeChains(VD, P->getCurScope());
    }

    // This does not suffice, as it only modifies the parser's scope, not the
    // semantic action's scope. It was previously paired with RemoveDecl right
    // after parsing.
    //P->getCurScope()->AddDecl(VD);

    // Parse the expression in an extended scope
    ExprResult E = P->ParseExpression();

    if (!E.isUsable())
      return consumeUntilClosingParenAndError(P);

    // TODO: in the case of trailing tokens (e.g. too many arguments), the error
    // message is not exactly mind-blowing
    if (P->getCurToken().getKind() != tok::r_paren)
      return consumeUntilClosingParenAndError(P);

    // From ParseAttributeArgsCommon, this seems like a sensible thing to do.
    SourceLocation RParen = P->getCurToken().getLocation();
    if (EndLoc)
      *EndLoc = RParen;

    P->ConsumeAnyToken();

    // We are done: register the ParsedAttr so that we see it later on.
    ArgsVector ArgExprs;
    ArgExprs.push_back(E.get());
    Attrs.addNew(AttrName, SourceRange(ScopeLoc, RParen), ScopeName, ScopeLoc,
                 ArgExprs.data(), ArgExprs.size(), ParsedAttr::AS_C2x);

    return AttributeApplied;
  }


  AttrHandling handleDeclAttribute(Sema &S, Decl *D,
                                   const ParsedAttr &Attr) const override {

    Expr *ArgExpr = Attr.getArgAsExpr(0);

    // This is super dirty because we can't yet add custom attributes, so we
    // have to rely on AnnotateAttr which can only hold a string! To make sure
    // we can tell our own attributes apart from potentially other plugins, we
    // pretty-print the expression now, and prefix it with c3d_FOO:.
    std::string Str = "c3d_constraint:";
    llvm::raw_string_ostream out{Str};
    ArgExpr->printPretty(out, nullptr, S.Context.getPrintingPolicy());
    LLVM_DEBUG(llvm::dbgs() << "c3d: registering constraint " << Str << "\n");

    // I tried to create a custom attribute that inherits from InheritableAttr
    // but I could not figure out how to implement its constructor (which is
    // deleted). I actually can't tell if plugins can even register new attributes
    // since it's all auto-generated (see
    // http://clang.llvm.org/docs/InternalsManual.html#AddingAttributes). So, at
    // this stage, it seems simpler to just render the expresion as a string
    // here...
    D->addAttr(AnnotateAttr::Create(S.Context, Str, Attr.getRange()));
    return AttributeApplied;
  }
};

class C3dParameterAttrInfo : public C3dSimpleSpelling, C3dDiagOnStruct {
public:
  C3dParameterAttrInfo():
    C3dSimpleSpelling("everparse::parameter"),
    C3dDiagOnStruct("everparse::parameter")
  {
    NumArgs = 1;
  }

  AttrHandling parseAttributePayload(Parser *P,
                                     ParsedAttributes &Attrs,
                                     Declarator *D,
                                     IdentifierInfo *AttrName,
                                     SourceLocation AttrNameLoc,
                                     SourceLocation *EndLoc,
                                     IdentifierInfo *ScopeName,
                                     SourceLocation ScopeLoc) const override {
    // Note: we don't have access to the internal API of the Parser here, which
    // makes things somewhat difficult. For instance, we don't have access to
    // ConsumeParen(), or ExpectAndConsume()...
    LLVM_DEBUG(llvm::dbgs() << "c3d: parsing argument to everparse::parameter\n");

    // Defer to the parser to produce a good error message. TODO is this right?
    if (P->getCurToken().getKind() != tok::l_paren)
      return AttributeNotApplied;

    // Eat opening left parenthesis.
    P->ConsumeAnyToken();

    // Parse the type -- no function is available to parse a declaration, sadly.
    TypeResult TR = P->ParseTypeName();
    if (!TR.isUsable())
      return consumeUntilClosingParenAndError(P);
    ParsedType PT = TR.get();

    // Parse the type of the parameter -- this is really a degenerate version of
    // parsing a proper spec and declarator, and only likely works for really
    // simple types.
    //
    // TODO: submit a patch to clang to be able to parse a simple spec-and-decl
    // in one go
    Token Tok = P->getCurToken();
    if (Tok.getKind() != tok::identifier)
      return consumeUntilClosingParenAndError(P);

    // Parse the name of the parameter. We LET the lookahead token be the ident.
    IdentifierInfo *ParamName = Tok.getIdentifierInfo();

    // Extend the scope with the parameter.
    LLVM_DEBUG(llvm::dbgs() << "c3d: parameter scope extension! " << ParamName->getNameStart() << "\n");
    Sema &S = P->getActions();

    // This doesn't work because it doesn't return the TypeSourceInfo.
    // QualType QT = PT.get();
    TypeSourceInfo *TS = nullptr;
    QualType QT = S.GetTypeFromParser(PT, &TS);
    LLVM_DEBUG(llvm::dbgs() << "c3d: parameter type: " << QT.getAsString() << "\n");

    // TODO: the locations are not exactly optimal here
    VarDecl *VD = VarDecl::Create(S.getASTContext(), S.CurContext,
        AttrNameLoc, AttrNameLoc, ParamName, QT,
        TS,
        SC_None);
    VD->setImplicit(true);
    S.PushOnScopeChains(VD, P->getCurScope());

    // Mega-hack; consumes the ident and encodes it as an expression... but
    // after we've added the ident into scope so as to avoid name resolution
    // errors. UGLY!
    ExprResult ER = P->ParseExpression();
    assert (ER.isUsable() && "This ident should have parsed");

    // TODO: in the case of trailing tokens (e.g. too many arguments), the error
    // message is not exactly mind-blowing
    if (P->getCurToken().getKind() != tok::r_paren)
      return consumeUntilClosingParenAndError(P);

    // From ParseAttributeArgsCommon, this seems like a sensible thing to do.
    SourceLocation RParen = P->getCurToken().getLocation();
    if (EndLoc)
      *EndLoc = RParen;

    P->ConsumeAnyToken();

    // Mega-hack: register two attributes with the same name, and rely on the
    // (unstated) invariant that clang preserves the order of things. The first
    // attribute will hold the type, and the subsequent one the expression.
    //
    // TODO: submit a patch to clang to allow a plugin-managed opaque_ptr in the
    // storage area of the ParsedAttr
    Attrs.addNewTypeAttr(AttrName, SourceRange(AttrNameLoc, RParen), ScopeName, ScopeLoc,
                 PT, ParsedAttr::AS_C2x);

    ArgsVector ArgExprs;
    ArgExprs.push_back(ER.get());
    Attrs.addNew(AttrName, SourceRange(AttrNameLoc, RParen), ScopeName, ScopeLoc,
                 ArgExprs.data(), ArgExprs.size(), ParsedAttr::AS_C2x);

    return AttributeApplied;
  }

  AttrHandling handleDeclAttribute(Sema &S, Decl *D,
                                   const ParsedAttr &Attr) const override {

    // 😱
    static const ParsedType *LastPT;
    static enum { SeenType, SeenExpr } State = SeenExpr;

    switch (State) {
      case SeenExpr:
        // Visiting a new pair of attributes, now seeing the type, which comes
        // first.
        LastPT = &Attr.getTypeArg();
        State = SeenType;
        return AttributeApplied;

      case SeenType: {
        Expr *ArgExpr = Attr.getArgAsExpr(0);

        std::string Str = "c3d_parameter:";
        llvm::raw_string_ostream out{Str};

        TypeSourceInfo *TS = nullptr;
        const QualType &QT = S.GetTypeFromParser(*LastPT, &TS);

        QT.print(out, S.Context.getPrintingPolicy());
        out << " ";
        ArgExpr->printPretty(out, nullptr, S.Context.getPrintingPolicy());

        LLVM_DEBUG(llvm::dbgs() << "c3d: registering parameter " << Str << "\n");

        D->addAttr(AnnotateAttr::Create(S.Context, Str, Attr.getRange()));

        State = SeenExpr;
        return AttributeApplied;
     }

     default: {
        /* Silences a GCC warning */
        LLVM_DEBUG(llvm::dbgs() << "c3d: WARNING default case in handleDeclAttribute\n");
        return NotHandled;
     }
    }
  }
};

class C3dWhereAttrInfo : public C3dSimpleSpelling, C3dDiagOnStruct {
public:
  C3dWhereAttrInfo():
    C3dSimpleSpelling("everparse::where"),
    C3dDiagOnStruct("everparse::where")
  {
    NumArgs = 1;
  }

  AttrHandling parseAttributePayload(Parser *P,
                                     ParsedAttributes &Attrs,
                                     Declarator *D,
                                     IdentifierInfo *AttrName,
                                     SourceLocation AttrNameLoc,
                                     SourceLocation *EndLoc,
                                     IdentifierInfo *ScopeName,
                                     SourceLocation ScopeLoc) const override {
    // Note: we don't have access to the internal API of the Parser here, which
    // makes things somewhat difficult. For instance, we don't have access to
    // ConsumeParen(), or ExpectAndConsume()...
    LLVM_DEBUG(llvm::dbgs() << "c3d: parsing argument to everparse::where\n");

    // Defer to the parser to produce a good error message. TODO is this right?
    if (P->getCurToken().getKind() != tok::l_paren)
      return AttributeNotApplied;

    // Eat opening left parenthesis.
    P->ConsumeAnyToken();

    ExprResult E;

    // We push a new scope and introduce a dummy 'this' variable
    // to parse the where clause. Then we pop it away, so it does
    // not leak.
    {
        // Push a new scope. We use the DeclScope flag which permits
        // declarations inside the new scope. Otherwise, we get
        // an assertion failure at the ExitScope(). (An alternative
        // is to manually delete the Decl from this new scope.)
        P->EnterScope(Scope::DeclScope);

        Sema &S = P->getActions();

        // A 'void' type
        const Type *voidTy = S.getASTContext().VoidTy.getTypePtr();
        QualType R = QualType(voidTy, 0);

        // A dummy 'this' identifier
        IdentifierInfo &IDD = P->getPreprocessor().getIdentifierTable().getOwn("this");

        // Create a variable declaration for 'this', at 'void' type, and push it.
        VarDecl *VD = VarDecl::Create(S.getASTContext(), S.CurContext,
                AttrNameLoc, AttrNameLoc, &IDD, R,
                nullptr,
                SC_None);
        VD->setImplicit(true);
        S.PushOnScopeChains(VD, P->getCurScope());

        // Parse the clause
        E = P->ParseExpression();

        // Pop the scope!
        P->ExitScope();
    }

    if (!E.isUsable())
      return consumeUntilClosingParenAndError(P);

    // TODO: in the case of trailing tokens (e.g. too many arguments), the error
    // message is not exactly mind-blowing
    if (P->getCurToken().getKind() != tok::r_paren)
      return consumeUntilClosingParenAndError(P);

    // From ParseAttributeArgsCommon, this seems like a sensible thing to do.
    SourceLocation RParen = P->getCurToken().getLocation();
    if (EndLoc)
      *EndLoc = RParen;

    P->ConsumeAnyToken();

    // We are done: register the ParsedAttr so that we see it later on.
    ArgsVector ArgExprs;
    ArgExprs.push_back(E.get());
    Attrs.addNew(AttrName, SourceRange(AttrNameLoc, RParen), ScopeName, ScopeLoc,
                 ArgExprs.data(), ArgExprs.size(), ParsedAttr::AS_C2x);

    return AttributeApplied;
  }

  AttrHandling handleDeclAttribute(Sema &S, Decl *D,
                                   const ParsedAttr &Attr) const override {

    // see C3dConstraintAttrInfo::handleDeclAttribute for explanation
    Expr *ArgExpr = Attr.getArgAsExpr(0);

    std::string Str = "c3d_where:";
    llvm::raw_string_ostream out{Str};
    ArgExpr->printPretty(out, nullptr, S.Context.getPrintingPolicy());
    LLVM_DEBUG(llvm::dbgs() << "c3d: registering where " << Str << "\n");

    D->addAttr(AnnotateAttr::Create(S.Context, Str, Attr.getRange()));
    return AttributeApplied;
  }
};

} // namespace

static ParsedAttrInfoRegistry::Add<C3dProcessAttrInfo> X1("c3d_process", "recognize everparse::process");
static ParsedAttrInfoRegistry::Add<C3dEntryPointAttrInfo> X2("c3d_entrypoint", "recognize everparse::entrypoint");
static ParsedAttrInfoRegistry::Add<C3dConstraintAttrInfo> X3("c3d_constraint", "recognize everparse::constraint");
static ParsedAttrInfoRegistry::Add<C3dParameterAttrInfo> X4("c3d_parameter", "recognize everparse::parameter");
static ParsedAttrInfoRegistry::Add<C3dWhereAttrInfo> X5("c3d_where", "recognize everparse::where");

//===----------------------------------------------------------------------===//

// Now that all the attributes have been validated, processed and retained in
// the AST via the annotate embedding, we perform our semantic action of:
// - removing struct fields that act as parameters -- they're not morally part
//   of the struct, and would be better suited to appear as arguments to
//   everparse::process, but attributes can only have expressions as arguments
//   (I can imagine some syntactic hack to embed a spec-and-declarator inside an
//   expression but let's leave this up to later).
// - emitting a .3d file as we process attributes in the AST
// - removing our annotations from the AST
//
// The documentation for this part is found at
// https://clang.llvm.org/docs/RAVFrontendAction.html, and
// https://freecompilercamp.org/clang-plugin/ also has a semi-complete
// example that half-works. Also note that many classes have excellent
// documentation in the headers, such as RecursiveASTVisitor.

#include "clang/Driver/Options.h"
#include "clang/AST/AST.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Rewrite/Core/Rewriter.h"

namespace {

using namespace std;

// The core of our rewriting-and-printing: this class identifies records that
// are marked to be processed with c3d annotations, then proceeds to generate a
// suitable .3d file while removing c3d-specific annotations or declarations from the AST.
//
// This class also performs a second task: it blits away the attributes from the
// original source file, via the rewriter, which then dumps out the original
// file with the attributes "masked out" as blanks.
class C3dVisitor : public RecursiveASTVisitor<C3dVisitor> {
private:
  ASTContext &AC;
  llvm::raw_fd_ostream& Out;


public:
  Rewriter R;

  virtual ~C3dVisitor () = default;

  explicit C3dVisitor(CompilerInstance *CI, llvm::raw_fd_ostream& Out)
    : AC((CI->getASTContext())),
      Out(Out),
      R(AC.getSourceManager(), AC.getLangOpts())
  {
  }

  bool VisitRecordDecl(RecordDecl *R) {
    LLVM_DEBUG(llvm::dbgs() << "c3d: visiting record " << R->getName() << "\n");

    // Iterate over this record's attributes, collecting non-c3d attributes in
    // filtered_attributes. We also remember some offsets for the first and last
    // attributes.
    bool HasProcess = false;
    bool HasEntrypoint = false;
    bool IsFirst = true;
    SourceLocation Start, End;
    AttrVec FilteredAttrs {};
    SmallVector<AnnotateAttr *, 4> Parameters {};
    SmallVector<AnnotateAttr *, 4> WhereClauses {};
    for (const auto& A: R->attrs()) {
      if (const auto& AA = dyn_cast<AnnotateAttr>(A)) {
        // Location-related business.
        if (IsFirst) {
          Start = AA->getLoc().getLocWithOffset(-6);
          IsFirst = false;
        }
        End = AA->getRange().getEnd().getLocWithOffset(4);

        LLVM_DEBUG(llvm::dbgs() << "c3d: record has attribute " << AA->getAnnotation() << "\n");
        if (AA->getAnnotation() == "c3d_process")
          HasProcess = true;
        else if (AA->getAnnotation() == "c3d_entrypoint")
          HasEntrypoint = true;
        else if (AA->getAnnotation().startswith("c3d_parameter:"))
          Parameters.push_back(AA);
        else if (AA->getAnnotation().startswith("c3d_where:"))
          WhereClauses.push_back(AA);
        else
          FilteredAttrs.push_back(AA);
      } else {
        FilteredAttrs.push_back(AA);
      }
    }

    // Early-abort.
    if (!HasProcess)
      return true;

    // Need to drop-then-assign, as just calling setAttrs triggers an assertion
    // failure.
    R->dropAttrs();
    R->setAttrs(FilteredAttrs);

    // Assuming no non-c3d attributes for now, meaning we can comment out the
    // entire attribute block.
    if (FilteredAttrs.size() > 0) {
      LLVM_DEBUG(llvm::dbgs() << "c3d: TODO: more fine-grained handling when existing atttributes for: " << R->getName() << "\n");
    } else if (!IsFirst) {
      // Based on SemaDeclAttr.cpp, specifically ProcessDeclAttributeList, it
      // seems like the range of the whole attribute list is not retained in any
      // meaningful way on the resulting Decl, so we have right now no way to
      // know where exactly the opening brackets are... so we do some guesswork
      // for the time being.
      //
      // TODO: do something smarter, perhaps use the cursor API to move
      // backwards until the token is found?
      LLVM_DEBUG(llvm::dbgs() << "c3d: record " << R->getName() << " commenting out attributes\n");
      this->R.InsertText(Start, "/*", true, true);
      this->R.InsertText(End, "*/", true, true);
    }

    // Interleaved printing
    if (HasEntrypoint)
      Out << "entrypoint\n";
    Out << "typedef struct ";
    Out << R->getName();

    // Printing parameters
    enum { BeforeLParen, InArgs } State = BeforeLParen;
    for (const auto& A: Parameters) {
      const int shift = strlen("c3d_parameter:");
      switch (State) {
        case BeforeLParen:
          Out << " (";
          Out << A->getAnnotation().slice(shift, A->getAnnotation().size());
          State = InArgs;
          break;
        case InArgs:
          Out << ", ";
          Out << A->getAnnotation().slice(shift, A->getAnnotation().size());
          break;
      }
    }
    if (State == InArgs)
      Out << ")";

    // Printing where clause, joining them into a single conjunction
    // since that's what 3d expects.
    if (! WhereClauses.empty()) {
        enum { First, Mid } State = First;
        const int shift = strlen("c3d_where:");
        Out << "\nwhere ";
        for (const auto& W: WhereClauses) {
            switch (State) {
                case Mid:
                    Out << " && ";
                    [[fallthrough]];

                case First:
                    Out << "(" << W->getAnnotation().slice(shift, W->getAnnotation().size()) << ")";
                    State = Mid;
                    break;
            }
        }
        Out << "\n";
    }

    Out << " { \n";

    LLVM_DEBUG(llvm::dbgs() << "c3d: everparse::process found (entrypoint: " << HasEntrypoint << "), reviewing fields\n");
    for (const auto& F: R->fields()) {
      LLVM_DEBUG(llvm::dbgs() << "c3d: visiting field " << F->getNameAsString() << "\n");
      bool IsFirst = true;
      SourceLocation Start, End;
      AttrVec FilteredAttributes {};
      SmallVector<StringRef, 4> FoundConstraints {};
      for (const auto& A: F->attrs()) {
        if (const auto& AA = dyn_cast<AnnotateAttr>(A)) {
          // Location-related business.
          if (IsFirst) {
            Start = AA->getLoc().getLocWithOffset(-4);
            IsFirst = false;
          }
          End = AA->getRange().getEnd().getLocWithOffset(3);

          StringRef Annot = AA->getAnnotation();
          LLVM_DEBUG(llvm::dbgs() << "c3d: " << F->getNameAsString() << " has an attribute " << Annot << "\n");
          if (Annot.startswith("c3d_constraint:"))
            FoundConstraints.push_back(Annot.slice(15, Annot.size()));
          else
            FilteredAttributes.push_back(A);
        } else {
          FilteredAttributes.push_back(A);
        }
      }
      F->dropAttrs();
      F->setAttrs(FilteredAttributes);

      if (FilteredAttributes.size() > 0) {
        LLVM_DEBUG(llvm::dbgs() << "c3d: TODO: more fine-grained handling when existing atttributes for: " << R->getName() << "\n");
      } else if (!IsFirst) {
        // Based on SemaDeclAttr.cpp, specifically ProcessDeclAttributeList, it
        // seems like the range of the whole attribute list is not retained in any
        // meaningful way on the resulting Decl, so we have right now no way to
        // know where exactly the opening brackets are... so we do some guesswork
        // for the time being.
        //
        // TODO: do something smarter, perhaps use the cursor API to move
        // backwards until the token is found?
        LLVM_DEBUG(llvm::dbgs() << "c3d: field " << F->getName() << " commenting out attributes\n");
        this->R.InsertText(Start, "/*", true, true);
        this->R.InsertText(End, "*/", true, true);
      }


      Out << "  ";
      F->print(Out, 2);
      if (FoundConstraints.size() > 0) {
        bool NeedsAnd = FoundConstraints.size() >= 2;
        Out << " { ";
        enum { FirstArg, NextArgs } PrintState = FirstArg;
        for (const auto &C: FoundConstraints) {
          if (PrintState == NextArgs)
            Out << " && ";
          if (NeedsAnd)
            Out << "(";
          Out << C;
          if (NeedsAnd)
            Out << ")";
          if (PrintState == FirstArg)
            PrintState = NextArgs;
        }
        Out << " } ";
      }
      Out << ";\n";
    }

    // Interleaved printing
    Out << "}\n\n";

    return true;
  }
};


// We register an instance of this class to allow modifying the AST.
class C3dASTConsumer : public ASTConsumer {
private:
  CompilerInstance *CI;

public:
  explicit C3dASTConsumer(CompilerInstance *CI_)
    : CI(CI_)
    { }

  void HandleTranslationUnit(ASTContext &Context) override {
    SourceManager& S = Context.getSourceManager();

    // Tedious string manipulations to figure out the destination file
    const FileEntry *E = S.getFileEntryForID(S.getMainFileID());
    StringRef File, Ext;
    std::tie(File, Ext) = E->getName().rsplit(".");
    std::string NewFile = "";
    NewFile += File;
    NewFile += ".3d";
    LLVM_DEBUG(llvm::dbgs() << "\n=== end of parsing & validation ===\n\n");
    LLVM_DEBUG(llvm::dbgs() << "c3d: will write in " << NewFile << "\n");

    // Open .3d file for writing
    std::error_code EC;
    llvm::raw_fd_ostream Out(NewFile, EC);
    // TODO: check EC

    // This also initializes the Rewriter V.R
    C3dVisitor V(CI, Out);

    LLVM_DEBUG(llvm::dbgs() << "c3d: starting AST rewrite\n");
    V.TraverseDecl(Context.getTranslationUnitDecl());

    // Now writing the cleaned up AST
    std::string OutputH;
    OutputH += File;
    OutputH += ".preprocessed.h";
    llvm::raw_fd_ostream OutH { OutputH, EC };

    // Our AST consumer has run and as a side-effect its Rewriter has
    // accumulated edits. Render the edited buffer into our preprocessed file.
    const RewriteBuffer &RewriteBuf = V.R.getEditBuffer(S.getMainFileID());
    RewriteBuf.write(OutH);

    return;
  }
};


// Registering the entry point for our AST rewriting.
//
// See https://clang.llvm.org/docs/ClangPlugins.html#writing-a-pluginastaction
// -- without this, -fplugin will NOT result in our plugin executing.
class PluginC3dAction : public PluginASTAction {
public:
  unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    return make_unique<C3dASTConsumer>(&CI);
  }

  bool ParseArgs(const CompilerInstance &CI, const vector<string> &args) override {
    return true;
  }

  // The default is CommandLine which does nothing. Override this behavior.
  ActionType getActionType() override {
    return AddAfterMainAction;
  }
};

} // namespace

static FrontendPluginRegistry::Add<PluginC3dAction>
    Y("c3d-plugin", "emit a 3d file write out a copy of the .h file stripped of its attributes");

