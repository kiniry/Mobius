/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;


public class DefaultVisitor extends Visitor {

  public void visitASTNode(ASTNode x) {
    // Assert.fail("DefaultVisitor.visitASTNode"+x);
  }

  public void visitModifierPragma(ModifierPragma x) {
  }

  public void visitTypeDeclElemPragma(TypeDeclElemPragma x) {
  }

  public void visitStmtPragma(StmtPragma x) {
  }

  public void visitTypeModifierPragma(TypeModifierPragma x) {
  }

  public void visitLexicalPragma(LexicalPragma x) {
  }


  public void visitCompilationUnit(CompilationUnit x) {
    for(int i=0; i<x.imports.size(); i++)
      x.imports.elementAt(i).accept( this );
    for(int i=0; i<x.elems.size(); i++)
      x.elems.elementAt(i).accept( this );
    if( x.lexicalPragmas != null ) 
	for(int i=0; i<x.lexicalPragmas.size(); i++)
	    x.lexicalPragmas.elementAt(i).accept( this );
  }

  public void visitTypeDecl(TypeDecl x) {
    for(int i=0; i<x.superInterfaces.size(); i++)
      x.superInterfaces.elementAt(i).accept( this );
    for(int i=0; i<x.elems.size(); i++)
      x.elems.elementAt(i).accept( this );
    if( x.pmodifiers != null ) 
	for(int i=0; i<x.pmodifiers.size(); i++)
	    x.pmodifiers.elementAt(i).accept( this );
    if( x.tmodifiers != null ) 
	for(int i=0; i<x.tmodifiers.size(); i++)
	    x.tmodifiers.elementAt(i).accept( this );
  }

  public void visitClassDecl(ClassDecl x) {
    if( x.superClass != null ) x.superClass.accept( this );
    visitTypeDecl(x);
  }

  public void visitInterfaceDecl(InterfaceDecl x) {
    visitTypeDecl(x);
  }

  public void visitRoutineDecl(RoutineDecl x) {
    for(int i=0; i<x.args.size(); i++)
      x.args.elementAt(i).accept( this );
    for(int i=0; i<x.raises.size(); i++)
      x.raises.elementAt(i).accept( this );
    if( x.pmodifiers != null ) 
	for(int i=0; i<x.pmodifiers.size(); i++)
	    x.pmodifiers.elementAt(i).accept( this );
    if( x.body != null ) x.body.accept( this );

  }

  public void visitConstructorDecl(ConstructorDecl x) {
    visitRoutineDecl(x);
    if( x.tmodifiers != null ) 
	for(int i=0; i<x.tmodifiers.size(); i++)
	    x.tmodifiers.elementAt(i).accept( this );
  }

  public void visitMethodDecl(MethodDecl x) {
    visitRoutineDecl(x);
    x.returnType.accept( this );
  }

  public void visitInitBlock(InitBlock x) {
    x.block.accept( this );
    if( x.pmodifiers != null ) 
	for(int i=0; i<x.pmodifiers.size(); i++)
	    x.pmodifiers.elementAt(i).accept( this );
  }

  public void visitGenericVarDecl(GenericVarDecl x) {
    if( x.pmodifiers != null ) 
	for(int i=0; i<x.pmodifiers.size(); i++)
	    x.pmodifiers.elementAt(i).accept( this );
    x.type.accept( this );
  }

  public void visitLocalVarDecl(LocalVarDecl x) {
    visitGenericVarDecl(x);
    if( x.init != null ) x.init.accept( this );
  }

  public void visitFieldDecl(FieldDecl x) {
    visitGenericVarDecl(x);
    if( x.init != null ) x.init.accept( this );
  }

  public void visitFormalParaDecl(FormalParaDecl x) {
    visitGenericVarDecl(x);
  }

  // ------------------------------

  public void visitGenericBlockStmt(GenericBlockStmt x) {
    for(int i=0; i<x.stmts.size(); i++)
      x.stmts.elementAt(i).accept( this );
  }

  public void visitBlockStmt(BlockStmt x) {
    visitGenericBlockStmt(x);
  }

  public void visitSwitchStmt(SwitchStmt x) {
    visitGenericBlockStmt(x);
    x.expr.accept( this );
  }

  public void visitClassDeclStmt(ClassDeclStmt x) {
    x.decl.accept( this );
  }

  public void visitVarDeclStmt(VarDeclStmt x) {
    x.decl.accept( this );
  }

  public void visitWhileStmt(WhileStmt x) {
    x.expr.accept( this );
    x.stmt.accept( this );
  }

  public void visitDoStmt(DoStmt x) {
    x.expr.accept( this );
    x.stmt.accept( this );
  }

  public void visitSynchronizeStmt(SynchronizeStmt x) {
    x.expr.accept( this );
    x.stmt.accept( this );
  }

  public void visitEvalStmt(EvalStmt x) {
    x.expr.accept( this );
  }

  public void visitReturnStmt(ReturnStmt x) {
    if( x.expr != null ) x.expr.accept( this );
  }

  public void visitThrowStmt(ThrowStmt x) {
    x.expr.accept( this );
  }

  public void visitBranchStmt(BranchStmt x) {
  }

  public void visitBreakStmt(BreakStmt x) {
  }

  public void visitContinueStmt(ContinueStmt x) {
  }

  public void visitLabelStmt(LabelStmt x) {
    x.stmt.accept( this );
  }

  public void visitIfStmt(IfStmt x) {
    x.expr.accept( this );
    x.thn.accept( this );
    x.els.accept( this );
  }

  public void visitForStmt(ForStmt x) {
    for(int i=0; i<x.forInit.size(); i++)
      x.forInit.elementAt(i).accept( this );
    x.test.accept( this );
    for(int i=0; i<x.forUpdate.size(); i++)
      x.forUpdate.elementAt(i).accept( this );
    x.body.accept( this );
  }

  public void visitSkipStmt(SkipStmt x) {
  }

  public void visitSwitchLabel(SwitchLabel x) {
    if( x.expr != null ) x.expr.accept( this );
  }

  public void visitTryFinallyStmt(TryFinallyStmt x) {
    x.tryClause.accept( this );
    x.finallyClause.accept( this );
  }

  public void visitTryCatchStmt(TryCatchStmt x) {
    x.tryClause.accept( this );
    for(int i=0; i<x.catchClauses.size(); i++)
      x.catchClauses.elementAt(i).accept( this );
  }

  public void visitConstructorInvocation(ConstructorInvocation x) {
    for(int i=0; i<x.args.size(); i++)
      x.args.elementAt(i).accept( this );
  }

  public void visitCatchClause(CatchClause x) {
    x.arg.accept( this );
    x.body.accept( this );
  }

  public void visitArrayInit(ArrayInit x) {
    for(int i=0; i<x.elems.size(); i++)
      x.elems.elementAt(i).accept( this );
  }

  public void visitExpr(Expr x) {
  }

  public void visitThisExpr(ThisExpr x) {
    if (x.classPrefix!=null)
	x.classPrefix.accept( this );
    visitExpr(x);
  }

  public void visitLiteralExpr(LiteralExpr x) {
    visitExpr(x);
  }

  public void visitArrayRefExpr(ArrayRefExpr x) {
    x.array.accept( this );
    x.index.accept( this );
    visitExpr(x);
  }

  public void visitNewInstanceExpr(NewInstanceExpr x) {
    x.type.accept( this );
    for(int i=0; i<x.args.size(); i++)
      x.args.elementAt(i).accept( this );
    if (x.anonDecl != null) x.anonDecl.accept( this );
    visitExpr(x);
  }

  public void visitNewArrayExpr(NewArrayExpr x) {
    x.type.accept( this );
    for(int i=0; i<x.dims.size(); i++)
      x.dims.elementAt(i).accept( this );
    if (x.init != null) x.init.accept( this );
    visitExpr(x);
  }

  public void visitCondExpr(CondExpr x) {
    x.test.accept( this );
    x.thn.accept( this );
    x.els.accept( this );
    visitExpr(x);
  }

  public void visitInstanceOfExpr(InstanceOfExpr x) {
    x.expr.accept( this );
    x.type.accept( this );
    visitExpr(x);
  }

  public void visitCastExpr(CastExpr x) {
    x.expr.accept( this );
    x.type.accept( this );
    visitExpr(x);
  }

  public void visitBinaryExpr(BinaryExpr x) {
    x.left.accept( this );
    x.right.accept( this );
    visitExpr(x);
  }

  public void visitUnaryExpr(UnaryExpr x) {
    x.expr.accept( this );
    visitExpr(x);
  }

  public void visitParenExpr(ParenExpr x) {
    x.expr.accept( this );
    visitExpr(x);
  }

  public void visitAmbiguousVariableAccess(AmbiguousVariableAccess x) {
    visitExpr(x);
  }

  public void visitVariableAccess(VariableAccess x) {
    visitExpr(x);
  }

  public void visitFieldAccess(FieldAccess x) {
    x.od.accept( this );
    visitExpr(x);
  }

  public void visitAmbiguousMethodInvocation(AmbiguousMethodInvocation x) {
    for(int i=0; i<x.args.size(); i++)
      x.args.elementAt(i).accept( this );
    visitExpr(x);
  }

  public void visitMethodInvocation(MethodInvocation x) {
    x.od.accept( this );
    for(int i=0; i<x.args.size(); i++)
      x.args.elementAt(i).accept( this );
    visitExpr(x);
  }

  public void visitClassLiteral(ClassLiteral x) {
    x.type.accept( this );
    visitExpr(x);
  }


  // ------------------------------

  public void visitExprObjectDesignator(ExprObjectDesignator x) {
    x.expr.accept( this );
    visitObjectDesignator(x);
  }

  public void visitTypeObjectDesignator(TypeObjectDesignator x) {
    x.type.accept( this );
    visitObjectDesignator(x);
  }

  public void visitSuperObjectDesignator(SuperObjectDesignator x) {
    visitObjectDesignator(x);
  }

  // ------------------------------

  public void visitPrimitiveType(PrimitiveType x) {
    visitType(x);
  }

  public void visitTypeName(TypeName x) {
    visitType(x);
  }

  public void visitArrayType(ArrayType x) {
    x.elemType.accept( this );
    visitType(x);
  }

  public void visitType(Type x) {
  }

  // ------------------------------

  public void visitName(Name x) {
  }
}
