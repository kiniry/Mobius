package jml2bml.rules;

import org.jmlspecs.openjml.JmlTreeVisitor;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSigOnly;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignals;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
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

  protected R preVisit(final Tree node, final P p) {
    return null;
  }

  @Override
  public R visitCompilationUnit(final CompilationUnitTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitImport(final ImportTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitClass(final ClassTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitMethod(final MethodTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitVariable(final VariableTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitEmptyStatement(final EmptyStatementTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitBlock(final BlockTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitDoWhileLoop(final DoWhileLoopTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitWhileLoop(final WhileLoopTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitForLoop(final ForLoopTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitEnhancedForLoop(final EnhancedForLoopTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitLabeledStatement(final LabeledStatementTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitSwitch(final SwitchTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitCase(final CaseTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitSynchronized(final SynchronizedTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitTry(final TryTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitCatch(final CatchTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitConditionalExpression(final ConditionalExpressionTree node,
                                           final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitIf(final IfTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitExpressionStatement(final ExpressionStatementTree node,
                                    final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitBreak(final BreakTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitContinue(final ContinueTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitReturn(final ReturnTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitThrow(final ThrowTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitAssert(final AssertTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitMethodInvocation(final MethodInvocationTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitNewClass(final NewClassTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitNewArray(final NewArrayTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitParenthesized(final ParenthesizedTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitAssignment(final AssignmentTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitCompoundAssignment(final CompoundAssignmentTree node,
                                   final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitUnary(final UnaryTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitBinary(final BinaryTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitTypeCast(final TypeCastTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitInstanceOf(final InstanceOfTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitArrayAccess(final ArrayAccessTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitMemberSelect(final MemberSelectTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitIdentifier(final IdentifierTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitLiteral(final LiteralTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitPrimitiveType(final PrimitiveTypeTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitArrayType(final ArrayTypeTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitParameterizedType(final ParameterizedTypeTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitTypeParameter(final TypeParameterTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitWildcard(final WildcardTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitModifiers(final ModifiersTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitAnnotation(final AnnotationTree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitOther(final Tree node, final P p) {
    return preVisit(node, p);
  }

  @Override
  public R visitErroneous(final ErroneousTree node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlBinary(final JmlBinary node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlClassDecl(final JmlClassDecl node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlCompilationUnit(final JmlCompilationUnit node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlDoWhileLoop(final JmlDoWhileLoop node, final P p) {
    return preVisit(node, p);

  }

  public R visitJmlEnhancedForLoop(final JmlEnhancedForLoop node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlForLoop(final JmlForLoop node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlGroupName(final JmlGroupName node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlImport(final JmlImport node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlLblExpression(final JmlLblExpression node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlMethodClauseAssignable(final JmlMethodClauseStoreRef node,
                                          final P p) {
    return preVisit(node, p);
  }

  public R visitJmlMethodClauseConditional(
     final JmlMethodClauseConditional node,
     final P p) {
    return preVisit(node, p);
  }

  public R visitJmlMethodClauseDecl(final JmlMethodClauseDecl node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlMethodClauseExpr(final JmlMethodClauseExpr node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlMethodClauseGroup(final JmlMethodClauseGroup node,
                                     final P p) {
    return preVisit(node, p);
  }

  public R visitJmlMethodClauseSigOnly(final JmlMethodClauseSigOnly node,
                                       final P p) {
    return preVisit(node, p);
  }

  public R visitJmlMethodClauseSignals(final JmlMethodClauseSignals node,
                                       final P p) {
    return preVisit(node, p);
  }

  public R visitJmlMethodDecl(final JmlMethodDecl node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlMethodSpecs(final JmlMethodSpecs node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlPrimitiveTypeTree(final JmlPrimitiveTypeTree node,
                                     final P p) {
    return preVisit(node, p);
  }

  public R visitJmlQuantifiedExpr(final JmlQuantifiedExpr node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlRefines(final JmlRefines node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlSetComprehension(final JmlSetComprehension node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlSingleton(final JmlSingleton node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlSpecificationCase(final JmlSpecificationCase node,
                                     final P p) {
    return preVisit(node, p);
  }

  public R visitJmlStatement(final JmlStatement node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlStatementDecls(final JmlStatementDecls node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlStatementExpr(final JmlStatementExpr node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlStatementLoop(final JmlStatementLoop node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlStatementSpec(final JmlStatementSpec node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlStoreRefArrayRange(final JmlStoreRefArrayRange node,
                                      final P p) {
    return preVisit(node, p);
  }

  public R visitJmlStoreRefKeyword(final JmlStoreRefKeyword node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlStoreRefListExpression(final JmlStoreRefListExpression node,
                                               final P p) {
    return preVisit(node, p);
  }

  public R visitJmlTypeClauseConditional(final JmlTypeClauseConditional node,
                                              final P p) {
    return preVisit(node, p);
  }

  public R visitJmlTypeClauseConstraint(final JmlTypeClauseConstraint node,
                                             final P p) {
    return preVisit(node, p);
  }

  public R visitJmlTypeClauseDecl(final JmlTypeClauseDecl node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlTypeClauseExpr(final JmlTypeClauseExpr node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlTypeClauseIn(final JmlTypeClauseIn node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlTypeClauseInitializer(final JmlTypeClauseInitializer node,
                                              final P p) {
    return preVisit(node, p);
  }

  public R visitJmlTypeClauseMaps(final JmlTypeClauseMaps node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlTypeClauseMonitorsFor(final JmlTypeClauseMonitorsFor node,
                                              final P p) {
    return preVisit(node, p);
  }

  public R visitJmlTypeClauseRepresents(final JmlTypeClauseRepresents node,
                                             final P p) {
    return preVisit(node, p);
  }

  public R visitJmlVariableDecl(final JmlVariableDecl node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlWhileLoop(final JmlWhileLoop node, final P p) {
    return preVisit(node, p);
  }

  public R visitJmlMethodInvocation(final JmlMethodInvocation node, final P p) {
    return preVisit(node, p);
  }
}
