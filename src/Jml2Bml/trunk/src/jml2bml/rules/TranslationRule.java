package jml2bml.rules;

import org.jmlspecs.openjml.JmlTreeVisitor;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlFunction;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseAssignable;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSigOnly;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignals;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlPrimitiveTypeTree;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlRefines;
import org.jmlspecs.openjml.JmlTree.JmlSetComprehension;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementDecls;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;
import org.jmlspecs.openjml.JmlTree.JmlStatementSpec;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefListExpression;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMonitorsFor;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;

import com.sun.source.tree.AnnotationTree;
import com.sun.source.tree.ArrayAccessTree;
import com.sun.source.tree.ArrayTypeTree;
import com.sun.source.tree.AssertTree;
import com.sun.source.tree.AssignmentTree;
import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.BlockTree;
import com.sun.source.tree.BreakTree;
import com.sun.source.tree.CaseTree;
import com.sun.source.tree.CatchTree;
import com.sun.source.tree.ClassTree;
import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.CompoundAssignmentTree;
import com.sun.source.tree.ConditionalExpressionTree;
import com.sun.source.tree.ContinueTree;
import com.sun.source.tree.DoWhileLoopTree;
import com.sun.source.tree.EmptyStatementTree;
import com.sun.source.tree.EnhancedForLoopTree;
import com.sun.source.tree.ErroneousTree;
import com.sun.source.tree.ExpressionStatementTree;
import com.sun.source.tree.ForLoopTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.IfTree;
import com.sun.source.tree.ImportTree;
import com.sun.source.tree.InstanceOfTree;
import com.sun.source.tree.LabeledStatementTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.ModifiersTree;
import com.sun.source.tree.NewArrayTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.ParameterizedTypeTree;
import com.sun.source.tree.ParenthesizedTree;
import com.sun.source.tree.PrimitiveTypeTree;
import com.sun.source.tree.ReturnTree;
import com.sun.source.tree.SwitchTree;
import com.sun.source.tree.SynchronizedTree;
import com.sun.source.tree.ThrowTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.TryTree;
import com.sun.source.tree.TypeCastTree;
import com.sun.source.tree.TypeParameterTree;
import com.sun.source.tree.UnaryTree;
import com.sun.source.tree.VariableTree;
import com.sun.source.tree.WhileLoopTree;
import com.sun.source.tree.WildcardTree;
import com.sun.source.util.TreeScanner;

public abstract class TranslationRule<R, P> extends TreeScanner<R, P>
    implements JmlTreeVisitor<R, P> {

  protected R preVisit(Tree node, P p) {
    return null;
  }

  public R visitCompilationUnit(CompilationUnitTree node, P p) {
    return preVisit(node, p);
  }

  public R visitImport(ImportTree node, P p) {
    return preVisit(node, p);
  }

  public R visitClass(ClassTree node, P p) {
    return preVisit(node, p);
  }

  public R visitMethod(MethodTree node, P p) {
    return preVisit(node, p);
  }

  public R visitVariable(VariableTree node, P p) {
    return preVisit(node, p);
  }

  public R visitEmptyStatement(EmptyStatementTree node, P p) {
    return preVisit(node, p);
  }

  public R visitBlock(BlockTree node, P p) {
    return preVisit(node, p);
  }

  public R visitDoWhileLoop(DoWhileLoopTree node, P p) {
    return preVisit(node, p);
  }

  public R visitWhileLoop(WhileLoopTree node, P p) {
    return preVisit(node, p);
  }

  public R visitForLoop(ForLoopTree node, P p) {
    return preVisit(node, p);
  }

  public R visitEnhancedForLoop(EnhancedForLoopTree node, P p) {
    return preVisit(node, p);
  }

  public R visitLabeledStatement(LabeledStatementTree node, P p) {
    return preVisit(node, p);
  }

  public R visitSwitch(SwitchTree node, P p) {
    return preVisit(node, p);
  }

  public R visitCase(CaseTree node, P p) {
    return preVisit(node, p);
  }

  public R visitSynchronized(SynchronizedTree node, P p) {
    return preVisit(node, p);
  }

  public R visitTry(TryTree node, P p) {
    return preVisit(node, p);
  }

  public R visitCatch(CatchTree node, P p) {
    return preVisit(node, p);
  }

  public R visitConditionalExpression(ConditionalExpressionTree node,
                                           P p) {
    return preVisit(node, p);
  }

  public R visitIf(IfTree node, P p) {
    return preVisit(node, p);
  }

  public R visitExpressionStatement(ExpressionStatementTree node, P p) {
    return preVisit(node, p);
  }

  public R visitBreak(BreakTree node, P p) {
    return preVisit(node, p);
  }

  public R visitContinue(ContinueTree node, P p) {
    return preVisit(node, p);
  }

  public R visitReturn(ReturnTree node, P p) {
    return preVisit(node, p);
  }

  public R visitThrow(ThrowTree node, P p) {
    return preVisit(node, p);
  }

  public R visitAssert(AssertTree node, P p) {
    return preVisit(node, p);
  }

  public R visitMethodInvocation(MethodInvocationTree node, P p) {
    return preVisit(node, p);
  }

  public R visitNewClass(NewClassTree node, P p) {
    return preVisit(node, p);
  }

  public R visitNewArray(NewArrayTree node, P p) {
    return preVisit(node, p);
  }

  public R visitParenthesized(ParenthesizedTree node, P p) {
    return preVisit(node, p);
  }

  public R visitAssignment(AssignmentTree node, P p) {
    return preVisit(node, p);
  }

  public R visitCompoundAssignment(CompoundAssignmentTree node, P p) {
    return preVisit(node, p);
  }

  public R visitUnary(UnaryTree node, P p) {
    return preVisit(node, p);
  }

  public R visitBinary(BinaryTree node, P p) {
    return preVisit(node, p);
  }

  public R visitTypeCast(TypeCastTree node, P p) {
    return preVisit(node, p);
  }

  public R visitInstanceOf(InstanceOfTree node, P p) {
    return preVisit(node, p);
  }

  public R visitArrayAccess(ArrayAccessTree node, P p) {
    return preVisit(node, p);
  }

  public R visitMemberSelect(MemberSelectTree node, P p) {
    return preVisit(node, p);
  }

  public R visitIdentifier(IdentifierTree node, P p) {
    return preVisit(node, p);
  }

  public R visitLiteral(LiteralTree node, P p) {
    return preVisit(node, p);
  }

  public R visitPrimitiveType(PrimitiveTypeTree node, P p) {
    return preVisit(node, p);
  }

  public R visitArrayType(ArrayTypeTree node, P p) {
    return preVisit(node, p);
  }

  public R visitParameterizedType(ParameterizedTypeTree node, P p) {
    return preVisit(node, p);
  }

  public R visitTypeParameter(TypeParameterTree node, P p) {
    return preVisit(node, p);
  }

  public R visitWildcard(WildcardTree node, P p) {
    return preVisit(node, p);
  }

  public R visitModifiers(ModifiersTree node, P p) {
    return preVisit(node, p);
  }

  public R visitAnnotation(AnnotationTree node, P p) {
    return preVisit(node, p);
  }

  public R visitOther(Tree node, P p) {
    return preVisit(node, p);
  }

  public R visitErroneous(ErroneousTree node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlBinary(JmlBinary node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlClassDecl(JmlClassDecl node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlCompilationUnit(JmlCompilationUnit node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlDoWhileLoop(JmlDoWhileLoop node, P p) {
    return preVisit(node, p);

  }

  @Override
  public R visitJmlEnhancedForLoop(JmlEnhancedForLoop node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlForLoop(JmlForLoop node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlFunction(JmlFunction node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlGroupName(JmlGroupName node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlImport(JmlImport node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlLblExpression(JmlLblExpression node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlMethodClauseAssignable(JmlMethodClauseAssignable node,
                                               P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlMethodClauseConditional(
                                                JmlMethodClauseConditional node,
                                                P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlMethodClauseDecl(JmlMethodClauseDecl node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlMethodClauseExpr(JmlMethodClauseExpr node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlMethodClauseGroup(JmlMethodClauseGroup node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlMethodClauseSignals(JmlMethodClauseSignals node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlMethodDecl(JmlMethodDecl node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlMethodSpecs(JmlMethodSpecs node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlQuantifiedExpr(JmlQuantifiedExpr node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlRefines(JmlRefines node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlSetComprehension(JmlSetComprehension node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlSingleton(JmlSingleton node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlSpecificationCase(JmlSpecificationCase node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlStatement(JmlStatement node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlStatementDecls(JmlStatementDecls node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlStatementExpr(JmlStatementExpr node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlStatementLoop(JmlStatementLoop node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlStatementSpec(JmlStatementSpec node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlStoreRefArrayRange(JmlStoreRefArrayRange node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlStoreRefKeyword(JmlStoreRefKeyword node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlStoreRefListExpression(JmlStoreRefListExpression node,
                                               P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlTypeClauseConditional(JmlTypeClauseConditional node,
                                              P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlTypeClauseConstraint(JmlTypeClauseConstraint node,
                                             P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlTypeClauseDecl(JmlTypeClauseDecl node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlTypeClauseExpr(JmlTypeClauseExpr node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlTypeClauseIn(JmlTypeClauseIn node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlTypeClauseInitializer(JmlTypeClauseInitializer node,
                                              P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlTypeClauseMaps(JmlTypeClauseMaps node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor node,
                                              P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlTypeClauseRepresents(JmlTypeClauseRepresents node,
                                             P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlVariableDecl(JmlVariableDecl node, P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitJmlWhileLoop(JmlWhileLoop node, P p) {
    return preVisit(node, p);
  }

}
