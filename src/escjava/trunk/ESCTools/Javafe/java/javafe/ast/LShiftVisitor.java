/**
 * $Id$
 *
 * @title "Visitor for Detection of LeftShift Incompleteness cases"
 * @description "Walks through an AST and finds any cases where the left
 * shift operator is used. It then adds a warning to ErrorSet about this"
 */

package javafe.ast;

import javafe.util.Location;
import javafe.util.ErrorSet;

public class LShiftVisitor extends ASTVisitor {

  public void visitASTNode(/*@ non_null */ ASTNode x) {
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

  public void visitCompilationUnit(/*@ non_null */ CompilationUnit x) {
    visitASTNode(x);
  }

  public void visitImportDecl(/*@ non_null */ ImportDecl x) {
    visitASTNode(x);
  }

  public void visitSingleTypeImportDecl(/*@ non_null */ SingleTypeImportDecl x) {
    visitImportDecl(x);
  }

  public void visitOnDemandImportDecl(/*@ non_null */ OnDemandImportDecl x) {
    visitImportDecl(x);
  }

  public void visitTypeDecl(/*@ non_null */ TypeDecl x) {
    visitASTNode(x);
  }

  public void visitClassDecl(/*@ non_null */ ClassDecl x) {
    visitTypeDecl(x);
  }

  public void visitInterfaceDecl(/*@ non_null */ InterfaceDecl x) {
    visitTypeDecl(x);
  }

  public void visitRoutineDecl(/*@ non_null */ RoutineDecl x) {
    visitASTNode(x);
  }

  public void visitConstructorDecl(/*@ non_null */ ConstructorDecl x) {
    visitRoutineDecl(x);
  }

  public void visitMethodDecl(/*@ non_null */ MethodDecl x) {
    visitRoutineDecl(x);
  }

  public void visitInitBlock(/*@ non_null */ InitBlock x) {
    visitASTNode(x);
  }

  public void visitTypeDeclElemPragma(/*@ non_null */ TypeDeclElemPragma x) {
    visitASTNode(x);
  }

  public void visitGenericVarDecl(/*@ non_null */ GenericVarDecl x) {
    visitASTNode(x);
  }

  public void visitLocalVarDecl(/*@ non_null */ LocalVarDecl x) {
    visitGenericVarDecl(x);
  }

  public void visitFieldDecl(/*@ non_null */ FieldDecl x) {
    visitGenericVarDecl(x);
  }

  public void visitFormalParaDecl(/*@ non_null */ FormalParaDecl x) {
    visitGenericVarDecl(x);
  }

  public void visitStmt(/*@ non_null */ Stmt x) {
    visitASTNode(x);
  }

  public void visitGenericBlockStmt(/*@ non_null */ GenericBlockStmt x) {
    visitStmt(x);
  }

  public void visitBlockStmt(/*@ non_null */ BlockStmt x) {
    visitGenericBlockStmt(x);
  }

  public void visitSwitchStmt(/*@ non_null */ SwitchStmt x) {
    visitGenericBlockStmt(x);
  }

  public void visitAssertStmt(/*@ non_null */ AssertStmt x) {
    visitStmt(x);
  }

  public void visitVarDeclStmt(/*@ non_null */ VarDeclStmt x) {
    visitStmt(x);
  }

  public void visitClassDeclStmt(/*@ non_null */ ClassDeclStmt x) {
    visitStmt(x);
  }

  public void visitWhileStmt(/*@ non_null */ WhileStmt x) {
    visitStmt(x);
  }

  public void visitDoStmt(/*@ non_null */ DoStmt x) {
    visitStmt(x);
  }

  public void visitSynchronizeStmt(/*@ non_null */ SynchronizeStmt x) {
    visitStmt(x);
  }

  public void visitEvalStmt(/*@ non_null */ EvalStmt x) {
    visitStmt(x);
  }

  public void visitReturnStmt(/*@ non_null */ ReturnStmt x) {
    visitStmt(x);
  }

  public void visitThrowStmt(/*@ non_null */ ThrowStmt x) {
    visitStmt(x);
  }

  public void visitBranchStmt(/*@ non_null */ BranchStmt x) {
    visitStmt(x);
  }

  public void visitBreakStmt(/*@ non_null */ BreakStmt x) {
    visitBranchStmt(x);
  }

  public void visitContinueStmt(/*@ non_null */ ContinueStmt x) {
    visitBranchStmt(x);
  }

  public void visitLabelStmt(/*@ non_null */ LabelStmt x) {
    visitStmt(x);
  }

  public void visitIfStmt(/*@ non_null */ IfStmt x) {
    visitStmt(x);
  }

  public void visitForStmt(/*@ non_null */ ForStmt x) {
    visitStmt(x);
  }

  public void visitSkipStmt(/*@ non_null */ SkipStmt x) {
    visitStmt(x);
  }

  public void visitSwitchLabel(/*@ non_null */ SwitchLabel x) {
    visitStmt(x);
  }

  public void visitTryFinallyStmt(/*@ non_null */ TryFinallyStmt x) {
    visitStmt(x);
  }

  public void visitTryCatchStmt(/*@ non_null */ TryCatchStmt x) {
    visitStmt(x);
  }

  public void visitStmtPragma(/*@ non_null */ StmtPragma x) {
    visitStmt(x);
  }

  public void visitConstructorInvocation(/*@ non_null */ ConstructorInvocation x) {
    visitStmt(x);
  }

  public void visitCatchClause(/*@ non_null */ CatchClause x) {
    visitASTNode(x);
  }

  public void visitVarInit(/*@ non_null */ VarInit x) {
    visitASTNode(x);
  }

  public void visitArrayInit(/*@ non_null */ ArrayInit x) {
    visitVarInit(x);
  }

  public void visitExpr(/*@ non_null */ Expr x) {
    visitVarInit(x);
  }

  public void visitThisExpr(/*@ non_null */ ThisExpr x) {
    visitExpr(x);
  }

  public void visitLiteralExpr(/*@ non_null */ LiteralExpr x) {
    visitExpr(x);
  }

  public void visitArrayRefExpr(/*@ non_null */ ArrayRefExpr x) {
    visitExpr(x);
  }

  public void visitNewInstanceExpr(/*@ non_null */ NewInstanceExpr x) {
    visitExpr(x);
  }

  public void visitNewArrayExpr(/*@ non_null */ NewArrayExpr x) {
    visitExpr(x);
  }

  public void visitCondExpr(/*@ non_null */ CondExpr x) {
    visitExpr(x);
  }

  public void visitInstanceOfExpr(/*@ non_null */ InstanceOfExpr x) {
    visitExpr(x);
  }

  public void visitCastExpr(/*@ non_null */ CastExpr x) {
    visitExpr(x);
  }

  public void visitBinaryExpr(/*@ non_null */ BinaryExpr x) {
    // if the binary expression contains the left shift operator warn about
    // it
    if(x.getTag() == TagConstants.LSHIFT || x.getTag() == TagConstants.ASGLSHIFT) {
      ErrorSet.warning(x.getStartLoc(), "The semantics of the left shift operator are incomplete.");
    }
    visitExpr(x);
  }

  public void visitUnaryExpr(/*@ non_null */ UnaryExpr x) {
    visitExpr(x);
  }

  public void visitParenExpr(/*@ non_null */ ParenExpr x) {
    visitExpr(x);
  }

  public void visitAmbiguousVariableAccess(/*@ non_null */ AmbiguousVariableAccess x) {
    visitExpr(x);
  }

  public void visitVariableAccess(/*@ non_null */ VariableAccess x) {
    visitExpr(x);
  }

  public void visitFieldAccess(/*@ non_null */ FieldAccess x) {
    visitExpr(x);
  }

  public void visitAmbiguousMethodInvocation(/*@ non_null */ AmbiguousMethodInvocation x) {
    visitExpr(x);
  }

  public void visitMethodInvocation(/*@ non_null */ MethodInvocation x) {
    visitExpr(x);
  }

  public void visitClassLiteral(/*@ non_null */ ClassLiteral x) {
    visitExpr(x);
  }

  public void visitObjectDesignator(/*@ non_null */ ObjectDesignator x) {
    visitASTNode(x);
  }

  public void visitExprObjectDesignator(/*@ non_null */ ExprObjectDesignator x) {
    visitObjectDesignator(x);
  }

  public void visitTypeObjectDesignator(/*@ non_null */ TypeObjectDesignator x) {
    visitObjectDesignator(x);
  }

  public void visitSuperObjectDesignator(/*@ non_null */ SuperObjectDesignator x) {
    visitObjectDesignator(x);
  }

  public void visitType(/*@ non_null */ Type x) {
    visitASTNode(x);
  }

  public void visitErrorType(/*@ non_null */ ErrorType x) {
    visitType(x);
  }

  public void visitPrimitiveType(/*@ non_null */ PrimitiveType x) {
    visitType(x);
  }

  public void visitTypeName(/*@ non_null */ TypeName x) {
    visitType(x);
  }

  public void visitArrayType(/*@ non_null */ ArrayType x) {
    visitType(x);
  }

  public void visitName(/*@ non_null */ Name x) {
    visitASTNode(x);
  }

  public void visitSimpleName(/*@ non_null */ SimpleName x) {
    visitName(x);
  }

  public void visitCompoundName(/*@ non_null */ CompoundName x) {
    visitName(x);
  }

  public void visitModifierPragma(/*@ non_null */ ModifierPragma x) {
    visitASTNode(x);
  }

  public void visitLexicalPragma(/*@ non_null */ LexicalPragma x) {
    visitASTNode(x);
  }

    public void visitTypeModifierPragma(/*@ non_null */ TypeModifierPragma x) {
    visitASTNode(x);
  }

}
