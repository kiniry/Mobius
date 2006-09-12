/**
 * RShiftVisitor.java
 *
 * @title "Visitor for Detection of RightShift Incompleteness cases"
 * @description "Walks through an AST and finds any cases where the right
 * shift operator is used. It then adds a warning to ErrorSet about this"
 */

package javafe.ast;

import javafe.util.ErrorSet;

public class RShiftVisitor extends Visitor {
  //@ requires x != null;
  public void visitASTNode(ASTNode x) {
    // a child of this node
    Object child = null;
    // temporary ASTNode
    ASTNode temp = null;
    // visit each child in this ASTNode if the child is an ASTNode
    for(int count = 0; count < x.childCount(); count++) {
      child = x.childAt(count);
      if(child instanceof ASTNode) {
        temp = (ASTNode) child;
        temp.accept(this);
      }
    }
  }

  //@ requires x != null;
  public void visitCompilationUnit(CompilationUnit x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitImportDecl(ImportDecl x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitSingleTypeImportDecl(SingleTypeImportDecl x) {
    visitImportDecl(x);
  }

  //@ requires x != null;
  public void visitOnDemandImportDecl(OnDemandImportDecl x) {
    visitImportDecl(x);
  }

  //@ requires x != null;
  public void visitTypeDecl(TypeDecl x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitClassDecl(ClassDecl x) {
    visitTypeDecl(x);
  }

  //@ requires x != null;
  public void visitInterfaceDecl(InterfaceDecl x) {
    visitTypeDecl(x);
  }

  //@ requires x != null;
  public void visitRoutineDecl(RoutineDecl x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitConstructorDecl(ConstructorDecl x) {
    visitRoutineDecl(x);
  }

  //@ requires x != null;
  public void visitMethodDecl(MethodDecl x) {
    visitRoutineDecl(x);
  }

  //@ requires x != null;
  public void visitInitBlock(InitBlock x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitTypeDeclElemPragma(TypeDeclElemPragma x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitGenericVarDecl(GenericVarDecl x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitLocalVarDecl(LocalVarDecl x) {
    visitGenericVarDecl(x);
  }

  //@ requires x != null;
  public void visitFieldDecl(FieldDecl x) {
    visitGenericVarDecl(x);
  }

  //@ requires x != null;
  public void visitFormalParaDecl(FormalParaDecl x) {
    visitGenericVarDecl(x);
  }

  //@ requires x != null;
  public void visitStmt(Stmt x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitGenericBlockStmt(GenericBlockStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitBlockStmt(BlockStmt x) {
    visitGenericBlockStmt(x);
  }

  //@ requires x != null;
  public void visitSwitchStmt(SwitchStmt x) {
    visitGenericBlockStmt(x);
  }

  //@ requires x != null;
  public void visitAssertStmt(AssertStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitVarDeclStmt(VarDeclStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitClassDeclStmt(ClassDeclStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitWhileStmt(WhileStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitDoStmt(DoStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitSynchronizeStmt(SynchronizeStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitEvalStmt(EvalStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitReturnStmt(ReturnStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitThrowStmt(ThrowStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitBranchStmt(BranchStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitBreakStmt(BreakStmt x) {
    visitBranchStmt(x);
  }

  //@ requires x != null;
  public void visitContinueStmt(ContinueStmt x) {
    visitBranchStmt(x);
  }

  //@ requires x != null;
  public void visitLabelStmt(LabelStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitIfStmt(IfStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitForStmt(ForStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitSkipStmt(SkipStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitSwitchLabel(SwitchLabel x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitTryFinallyStmt(TryFinallyStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitTryCatchStmt(TryCatchStmt x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitStmtPragma(StmtPragma x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitConstructorInvocation(ConstructorInvocation x) {
    visitStmt(x);
  }

  //@ requires x != null;
  public void visitCatchClause(CatchClause x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitVarInit(VarInit x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitArrayInit(ArrayInit x) {
    visitVarInit(x);
  }

  //@ requires x != null;
  public void visitExpr(Expr x) {
    visitVarInit(x);
  }

  //@ requires x != null;
  public void visitThisExpr(ThisExpr x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitLiteralExpr(LiteralExpr x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitArrayRefExpr(ArrayRefExpr x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitNewInstanceExpr(NewInstanceExpr x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitNewArrayExpr(NewArrayExpr x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitCondExpr(CondExpr x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitInstanceOfExpr(InstanceOfExpr x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitCastExpr(CastExpr x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitBinaryExpr(BinaryExpr x) {
    // if the binary expression contains the right shift operator warn about
    // it
    if(x.getTag() == TagConstants.RSHIFT || x.getTag() == TagConstants.ASGRSHIFT) {
      ErrorSet.warning(x.getStartLoc(), "The semantics of the right shift operator are incomplete.");
    }
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitUnaryExpr(UnaryExpr x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitParenExpr(ParenExpr x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitAmbiguousVariableAccess(AmbiguousVariableAccess x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitVariableAccess(VariableAccess x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitFieldAccess(FieldAccess x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitAmbiguousMethodInvocation(AmbiguousMethodInvocation x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitMethodInvocation(MethodInvocation x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitClassLiteral(ClassLiteral x) {
    visitExpr(x);
  }

  //@ requires x != null;
  public void visitObjectDesignator(ObjectDesignator x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitExprObjectDesignator(ExprObjectDesignator x) {
    visitObjectDesignator(x);
  }

  //@ requires x != null;
  public void visitTypeObjectDesignator(TypeObjectDesignator x) {
    visitObjectDesignator(x);
  }

  //@ requires x != null;
  public void visitSuperObjectDesignator(SuperObjectDesignator x) {
    visitObjectDesignator(x);
  }

  //@ requires x != null;
  public void visitType(Type x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitErrorType(ErrorType x) {
    visitType(x);
  }

  //@ requires x != null;
  public void visitPrimitiveType(PrimitiveType x) {
    visitType(x);
  }

  //@ requires x != null;
  public void visitTypeName(TypeName x) {
    visitType(x);
  }

  //@ requires x != null;
  public void visitArrayType(ArrayType x) {
    visitType(x);
  }

  //@ requires x != null;
  public void visitName(Name x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitSimpleName(SimpleName x) {
    visitName(x);
  }

  //@ requires x != null;
  public void visitCompoundName(CompoundName x) {
    visitName(x);
  }

  //@ requires x != null;
  public void visitModifierPragma(ModifierPragma x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitLexicalPragma(LexicalPragma x) {
    visitASTNode(x);
  }

  //@ requires x != null;
  public void visitTypeModifierPragma(TypeModifierPragma x) {
    visitASTNode(x);
  }

}
