/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit

public abstract class VisitorArgResult {
  //@ requires x!=null
  //@ ensures \result!=null
  public abstract Object visitASTNode(ASTNode x, Object o);

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitCompilationUnit(CompilationUnit x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitImportDecl(ImportDecl x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSingleTypeImportDecl(SingleTypeImportDecl x, Object o) {
    return visitImportDecl(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitOnDemandImportDecl(OnDemandImportDecl x, Object o) {
    return visitImportDecl(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitTypeDecl(TypeDecl x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitClassDecl(ClassDecl x, Object o) {
    return visitTypeDecl(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitInterfaceDecl(InterfaceDecl x, Object o) {
    return visitTypeDecl(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitRoutineDecl(RoutineDecl x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitConstructorDecl(ConstructorDecl x, Object o) {
    return visitRoutineDecl(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitMethodDecl(MethodDecl x, Object o) {
    return visitRoutineDecl(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitInitBlock(InitBlock x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitTypeDeclElemPragma(TypeDeclElemPragma x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitGenericVarDecl(GenericVarDecl x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitLocalVarDecl(LocalVarDecl x, Object o) {
    return visitGenericVarDecl(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitFieldDecl(FieldDecl x, Object o) {
    return visitGenericVarDecl(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitFormalParaDecl(FormalParaDecl x, Object o) {
    return visitGenericVarDecl(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitStmt(Stmt x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitGenericBlockStmt(GenericBlockStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitBlockStmt(BlockStmt x, Object o) {
    return visitGenericBlockStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSwitchStmt(SwitchStmt x, Object o) {
    return visitGenericBlockStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitAssertStmt(AssertStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitVarDeclStmt(VarDeclStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitClassDeclStmt(ClassDeclStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitWhileStmt(WhileStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitDoStmt(DoStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSynchronizeStmt(SynchronizeStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitEvalStmt(EvalStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitReturnStmt(ReturnStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitThrowStmt(ThrowStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitBranchStmt(BranchStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitBreakStmt(BreakStmt x, Object o) {
    return visitBranchStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitContinueStmt(ContinueStmt x, Object o) {
    return visitBranchStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitLabelStmt(LabelStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitIfStmt(IfStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitForStmt(ForStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSkipStmt(SkipStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSwitchLabel(SwitchLabel x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitTryFinallyStmt(TryFinallyStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitTryCatchStmt(TryCatchStmt x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitStmtPragma(StmtPragma x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitConstructorInvocation(ConstructorInvocation x, Object o) {
    return visitStmt(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitCatchClause(CatchClause x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitVarInit(VarInit x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitArrayInit(ArrayInit x, Object o) {
    return visitVarInit(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitExpr(Expr x, Object o) {
    return visitVarInit(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitThisExpr(ThisExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitLiteralExpr(LiteralExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitArrayRefExpr(ArrayRefExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitNewInstanceExpr(NewInstanceExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitNewArrayExpr(NewArrayExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitCondExpr(CondExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitInstanceOfExpr(InstanceOfExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitCastExpr(CastExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitBinaryExpr(BinaryExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitUnaryExpr(UnaryExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitParenExpr(ParenExpr x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitAmbiguousVariableAccess(AmbiguousVariableAccess x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitVariableAccess(VariableAccess x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitFieldAccess(FieldAccess x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitAmbiguousMethodInvocation(AmbiguousMethodInvocation x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitMethodInvocation(MethodInvocation x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitClassLiteral(ClassLiteral x, Object o) {
    return visitExpr(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitObjectDesignator(ObjectDesignator x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitExprObjectDesignator(ExprObjectDesignator x, Object o) {
    return visitObjectDesignator(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitTypeObjectDesignator(TypeObjectDesignator x, Object o) {
    return visitObjectDesignator(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSuperObjectDesignator(SuperObjectDesignator x, Object o) {
    return visitObjectDesignator(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitType(Type x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitPrimitiveType(PrimitiveType x, Object o) {
    return visitType(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitTypeName(TypeName x, Object o) {
    return visitType(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitArrayType(ArrayType x, Object o) {
    return visitType(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitName(Name x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitSimpleName(SimpleName x, Object o) {
    return visitName(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitCompoundName(CompoundName x, Object o) {
    return visitName(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitModifierPragma(ModifierPragma x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitLexicalPragma(LexicalPragma x, Object o) {
    return visitASTNode(x, o);
  }

  //@ requires x!=null
  //@ ensures \result!=null
  public Object visitTypeModifierPragma(TypeModifierPragma x, Object o) {
    return visitASTNode(x, o);
  }

}
