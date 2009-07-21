// -*- mode: java -*-
/* Copyright 2000, 2001, Compaq Computer Corporation */

/* IF THIS IS A JAVA FILE, DO NOT EDIT IT!  

   Most Java files in this directory which are part of the Javafe AST
   are automatically generated using the astgen comment (see
   ESCTools/Javafe/astgen) from the input file 'hierarchy.h'.  If you
   wish to modify AST classes or introduce new ones, modify
   'hierarchy.j.'
 */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;
import javafe.tc.TagConstants;

// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit

public abstract class VisitorArgResult {
  public abstract /*@non_null*/ Object visitASTNode(/*@non_null*/ ASTNode x, Object o);

  public /*@non_null*/ Object visitCompilationUnit(/*@non_null*/ CompilationUnit x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitImportDecl(/*@non_null*/ ImportDecl x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitSingleTypeImportDecl(/*@non_null*/ SingleTypeImportDecl x, Object o) {
    return visitImportDecl(x, o);
  }

  public /*@non_null*/ Object visitOnDemandImportDecl(/*@non_null*/ OnDemandImportDecl x, Object o) {
    return visitImportDecl(x, o);
  }

  public /*@non_null*/ Object visitTypeDecl(/*@non_null*/ TypeDecl x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitClassDecl(/*@non_null*/ ClassDecl x, Object o) {
    return visitTypeDecl(x, o);
  }

  public /*@non_null*/ Object visitInterfaceDecl(/*@non_null*/ InterfaceDecl x, Object o) {
    return visitTypeDecl(x, o);
  }

  public /*@non_null*/ Object visitRoutineDecl(/*@non_null*/ RoutineDecl x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitConstructorDecl(/*@non_null*/ ConstructorDecl x, Object o) {
    return visitRoutineDecl(x, o);
  }

  public /*@non_null*/ Object visitMethodDecl(/*@non_null*/ MethodDecl x, Object o) {
    return visitRoutineDecl(x, o);
  }

  public /*@non_null*/ Object visitInitBlock(/*@non_null*/ InitBlock x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitTypeDeclElemPragma(/*@non_null*/ TypeDeclElemPragma x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitGenericVarDecl(/*@non_null*/ GenericVarDecl x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitLocalVarDecl(/*@non_null*/ LocalVarDecl x, Object o) {
    return visitGenericVarDecl(x, o);
  }

  public /*@non_null*/ Object visitFieldDecl(/*@non_null*/ FieldDecl x, Object o) {
    return visitGenericVarDecl(x, o);
  }

  public /*@non_null*/ Object visitFormalParaDecl(/*@non_null*/ FormalParaDecl x, Object o) {
    return visitGenericVarDecl(x, o);
  }

  public /*@non_null*/ Object visitStmt(/*@non_null*/ Stmt x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitGenericBlockStmt(/*@non_null*/ GenericBlockStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitBlockStmt(/*@non_null*/ BlockStmt x, Object o) {
    return visitGenericBlockStmt(x, o);
  }

  public /*@non_null*/ Object visitSwitchStmt(/*@non_null*/ SwitchStmt x, Object o) {
    return visitGenericBlockStmt(x, o);
  }

  public /*@non_null*/ Object visitAssertStmt(/*@non_null*/ AssertStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitVarDeclStmt(/*@non_null*/ VarDeclStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitClassDeclStmt(/*@non_null*/ ClassDeclStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitWhileStmt(/*@non_null*/ WhileStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitDoStmt(/*@non_null*/ DoStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitSynchronizeStmt(/*@non_null*/ SynchronizeStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitEvalStmt(/*@non_null*/ EvalStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitReturnStmt(/*@non_null*/ ReturnStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitThrowStmt(/*@non_null*/ ThrowStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitBranchStmt(/*@non_null*/ BranchStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitBreakStmt(/*@non_null*/ BreakStmt x, Object o) {
    return visitBranchStmt(x, o);
  }

  public /*@non_null*/ Object visitContinueStmt(/*@non_null*/ ContinueStmt x, Object o) {
    return visitBranchStmt(x, o);
  }

  public /*@non_null*/ Object visitLabelStmt(/*@non_null*/ LabelStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitIfStmt(/*@non_null*/ IfStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitForStmt(/*@non_null*/ ForStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitSkipStmt(/*@non_null*/ SkipStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitSwitchLabel(/*@non_null*/ SwitchLabel x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitTryFinallyStmt(/*@non_null*/ TryFinallyStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitTryCatchStmt(/*@non_null*/ TryCatchStmt x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitStmtPragma(/*@non_null*/ StmtPragma x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitConstructorInvocation(/*@non_null*/ ConstructorInvocation x, Object o) {
    return visitStmt(x, o);
  }

  public /*@non_null*/ Object visitCatchClause(/*@non_null*/ CatchClause x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitVarInit(/*@non_null*/ VarInit x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitArrayInit(/*@non_null*/ ArrayInit x, Object o) {
    return visitVarInit(x, o);
  }

  public /*@non_null*/ Object visitExpr(/*@non_null*/ Expr x, Object o) {
    return visitVarInit(x, o);
  }

  public /*@non_null*/ Object visitThisExpr(/*@non_null*/ ThisExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitLiteralExpr(/*@non_null*/ LiteralExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitArrayRefExpr(/*@non_null*/ ArrayRefExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitNewInstanceExpr(/*@non_null*/ NewInstanceExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitNewArrayExpr(/*@non_null*/ NewArrayExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitCondExpr(/*@non_null*/ CondExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitInstanceOfExpr(/*@non_null*/ InstanceOfExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitCastExpr(/*@non_null*/ CastExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitBinaryExpr(/*@non_null*/ BinaryExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitUnaryExpr(/*@non_null*/ UnaryExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitParenExpr(/*@non_null*/ ParenExpr x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitAmbiguousVariableAccess(/*@non_null*/ AmbiguousVariableAccess x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitVariableAccess(/*@non_null*/ VariableAccess x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitFieldAccess(/*@non_null*/ FieldAccess x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitAmbiguousMethodInvocation(/*@non_null*/ AmbiguousMethodInvocation x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitMethodInvocation(/*@non_null*/ MethodInvocation x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitClassLiteral(/*@non_null*/ ClassLiteral x, Object o) {
    return visitExpr(x, o);
  }

  public /*@non_null*/ Object visitObjectDesignator(/*@non_null*/ ObjectDesignator x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitExprObjectDesignator(/*@non_null*/ ExprObjectDesignator x, Object o) {
    return visitObjectDesignator(x, o);
  }

  public /*@non_null*/ Object visitTypeObjectDesignator(/*@non_null*/ TypeObjectDesignator x, Object o) {
    return visitObjectDesignator(x, o);
  }

  public /*@non_null*/ Object visitSuperObjectDesignator(/*@non_null*/ SuperObjectDesignator x, Object o) {
    return visitObjectDesignator(x, o);
  }

  public /*@non_null*/ Object visitType(/*@non_null*/ Type x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitErrorType(/*@non_null*/ ErrorType x, Object o) {
    return visitType(x, o);
  }

  public /*@non_null*/ Object visitPrimitiveType(/*@non_null*/ PrimitiveType x, Object o) {
    return visitType(x, o);
  }

  public /*@non_null*/ Object visitJavafePrimitiveType(/*@non_null*/ JavafePrimitiveType x, Object o) {
    return visitPrimitiveType(x, o);
  }

  public /*@non_null*/ Object visitTypeName(/*@non_null*/ TypeName x, Object o) {
    return visitType(x, o);
  }

  public /*@non_null*/ Object visitArrayType(/*@non_null*/ ArrayType x, Object o) {
    return visitType(x, o);
  }

  public /*@non_null*/ Object visitName(/*@non_null*/ Name x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitSimpleName(/*@non_null*/ SimpleName x, Object o) {
    return visitName(x, o);
  }

  public /*@non_null*/ Object visitCompoundName(/*@non_null*/ CompoundName x, Object o) {
    return visitName(x, o);
  }

  public /*@non_null*/ Object visitModifierPragma(/*@non_null*/ ModifierPragma x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitLexicalPragma(/*@non_null*/ LexicalPragma x, Object o) {
    return visitASTNode(x, o);
  }

  public /*@non_null*/ Object visitTypeModifierPragma(/*@non_null*/ TypeModifierPragma x, Object o) {
    return visitASTNode(x, o);
  }

}
