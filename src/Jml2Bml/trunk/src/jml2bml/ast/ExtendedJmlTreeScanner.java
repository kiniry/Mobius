/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.ast;

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

/**
 * This class adds to the TreeScanner<R,P> the preVisit method (invoked at the
 * beginning of all visitXYZ methods).
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @param <R>
 * @param <P>
 * @version 0-0.1
 */
public class ExtendedJmlTreeScanner<R, P> extends TreeScanner < R, P >
    implements JmlTreeVisitor < R, P > {

  /**
   * visits the given node and returns the as a result reduction of given
   * parameter r and the result of visiting node.
   * @param node - node to visit
   * @param p - additional data
   * @param r - another visit result (for reduction)
   * @return - reduction of r and result of visiting node
   */
  private R scanAndReduce(final Tree node, final P p, final R r) {
    return reduce(scan(node, p), r);
  }

  /**
   * visits the given nodes and returns the as a result reduction of given
   * parameter r and the result of visiting nodes.
   * @param nodes - nodes to visit
   * @param p - additional data
   * @param r - another visit result (for reduction)
   * @return - reduction of r and result of visiting nodes
   */
  private R scanAndReduce(final Iterable < ? extends Tree > nodes, final P p,
                          final R r) {
    return reduce(scan(nodes, p), r);
  }

  /**
   * Method invoked before all visitXYZ methods.
   * @param node - visited node
   * @param p - additional data passed to the visit method.
   * Meaning of this field is determined in subclasses.
   * @return the given additional data. Should be overwritten in subclasses.
   */
  protected P preVisit(final Tree node, final P p) {
    return p;
  }

  /**
   * Visiting compilation unit node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitCompilationUnit(final CompilationUnitTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitCompilationUnit(node, tmpP);
  }

  /**
   * Visiting import node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitImport(final ImportTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitImport(node, tmpP);
  }

  /**
   * Visiting ClassTree node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitClass(final ClassTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitClass(node, tmpP);
  }

  /**
   * Visiting MethodTree node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitMethod(final MethodTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitMethod(node, tmpP);
  }

  /**
   * Visiting variableTree node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitVariable(final VariableTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitVariable(node, tmpP);
  }

  /**
   * Visiting empty statement node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitEmptyStatement(final EmptyStatementTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitEmptyStatement(node, tmpP);
  }

  /**
   * Visiting block node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitBlock(final BlockTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitBlock(node, tmpP);
  }

  /**
   * Visiting do-while loop node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitDoWhileLoop(final DoWhileLoopTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitDoWhileLoop(node, tmpP);
  }

  /**
   * Visiting while-loop node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitWhileLoop(final WhileLoopTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitWhileLoop(node, tmpP);
  }

  /**
   * Visiting for-loop node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitForLoop(final ForLoopTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitForLoop(node, tmpP);
  }

  /**
   * Visiting enhanced for loop node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitEnhancedForLoop(final EnhancedForLoopTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitEnhancedForLoop(node, tmpP);
  }

  /**
   * Visiting labeled statement node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitLabeledStatement(final LabeledStatementTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitLabeledStatement(node, tmpP);
  }

  /**
   * Visiting switch node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitSwitch(final SwitchTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitSwitch(node, tmpP);
  }

  /**
   * Visiting case node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitCase(final CaseTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitCase(node, tmpP);
  }

  /**
   * Visiting synchronized node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitSynchronized(final SynchronizedTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitSynchronized(node, tmpP);
  }

  /**
   * Visiting try node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitTry(final TryTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitTry(node, tmpP);
  }

  /**
   * Visiting catch node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitCatch(final CatchTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitCatch(node, tmpP);
  }

  /**
   * Visiting conditional expression node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitConditionalExpression(final ConditionalExpressionTree node,
                                      final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitConditionalExpression(node, tmpP);
  }

  /**
   * Visiting if node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitIf(final IfTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitIf(node, tmpP);
  }

  /**
   * Visiting expression statement node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitExpressionStatement(final ExpressionStatementTree node,
                                    final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitExpressionStatement(node, tmpP);
  }

  /**
   * Visiting break node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitBreak(final BreakTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitBreak(node, tmpP);
  }

  /**
   * Visiting continue node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitContinue(final ContinueTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitContinue(node, tmpP);
  }

  /**
   * Visiting return node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitReturn(final ReturnTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitReturn(node, tmpP);
  }

  /**
   * Visiting throw node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitThrow(final ThrowTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitThrow(node, tmpP);
  }

  /**
   * Visiting assert node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitAssert(final AssertTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitAssert(node, tmpP);
  }

  /**
   * Visiting method invocation node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitMethodInvocation(final MethodInvocationTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitMethodInvocation(node, tmpP);
  }

  /**
   * Visiting New Class node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitNewClass(final NewClassTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitNewClass(node, tmpP);
  }

  /**
   * Visiting new array node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitNewArray(final NewArrayTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitNewArray(node, tmpP);
  }

  /**
   * Visiting Parenthesized node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitParenthesized(final ParenthesizedTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitParenthesized(node, tmpP);
  }

  /**
   * Visiting assignment node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitAssignment(final AssignmentTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitAssignment(node, tmpP);
  }

  /**
   * Visiting compound assignment node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitCompoundAssignment(final CompoundAssignmentTree node,
                                   final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitCompoundAssignment(node, tmpP);
  }

  /**
   * Visiting Unary node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitUnary(final UnaryTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitUnary(node, tmpP);
  }

  /**
   * Visiting Binary node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitBinary(final BinaryTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitBinary(node, tmpP);
  }

  /**
   * Visiting type cast node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitTypeCast(final TypeCastTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitTypeCast(node, tmpP);
  }

  /**
   * Visiting instanceof node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitInstanceOf(final InstanceOfTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitInstanceOf(node, tmpP);
  }

  /**
   * Visiting array access node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitArrayAccess(final ArrayAccessTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitArrayAccess(node, tmpP);
  }

  /**
   * Visiting member select node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitMemberSelect(final MemberSelectTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitMemberSelect(node, tmpP);
  }

  /**
   * Visiting identifier node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitIdentifier(final IdentifierTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitIdentifier(node, tmpP);
  }

  /**
   * Visiting literal node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitLiteral(final LiteralTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitLiteral(node, tmpP);
  }

  /**
   * Visiting primitive type node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitPrimitiveType(final PrimitiveTypeTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitPrimitiveType(node, tmpP);
  }

  /**
   * Visiting array type node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitArrayType(final ArrayTypeTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitArrayType(node, tmpP);
  }

  /**
   * Visiting parameterized type node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitParameterizedType(final ParameterizedTypeTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitParameterizedType(node, tmpP);
  }

  /**
   * Visiting type parameter node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitTypeParameter(final TypeParameterTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitTypeParameter(node, tmpP);
  }

  /**
   * Visiting wildcard node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitWildcard(final WildcardTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitWildcard(node, tmpP);
  }

  /**
   * Visiting modifiers node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitModifiers(final ModifiersTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitModifiers(node, tmpP);
  }

  /**
   * Visiting annotation node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitAnnotation(final AnnotationTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitAnnotation(node, tmpP);
  }

  /**
   * Visiting other node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitOther(final Tree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitOther(node, tmpP);
  }

  /**
   * Visiting errorneous node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  @Override
  public R visitErroneous(final ErroneousTree node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitErroneous(node, tmpP);
  }

  /**
   * Visiting JmlBinary node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlBinary(final JmlBinary node, final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.lhs, tmpP);
    r = scanAndReduce(node.rhs, tmpP, r);
    return r;
  }

  /**
   * Visiting Jml class declaration node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlClassDecl(final JmlClassDecl node, final P p) {
    final P tmpP = preVisit(node, p);
    final R r = super.visitClass(node, tmpP);
    if (node.typeSpecs!=null){
      final R tmpR = scan(node.typeSpecs.clauses, tmpP);
      return reduce(r, tmpR);
    }
    return r;
  }

  /**
   * Visiting jml compilation unit node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlCompilationUnit(final JmlCompilationUnit node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitCompilationUnit(node, tmpP);
  }

  /**
   * Visiting jml do-while loop node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlDoWhileLoop(final JmlDoWhileLoop node, final P p) {
    final P tmpP = preVisit(node, p);
    final R r = scan(node.loopSpecs, tmpP);
    final R tmpR = super.visitDoWhileLoop(node, tmpP);
    return reduce(r, tmpR);
  }

  /**
   * Visiting jml enhanced for loop node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlEnhancedForLoop(final JmlEnhancedForLoop node, final P p) {
    final P tmpP = preVisit(node, p);
    final R r = scan(node.loopSpecs, tmpP);
    final R tmpR = super.visitEnhancedForLoop(node, tmpP);
    return reduce(r, tmpR);
  }

  /**
   * Visiting jml-for node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlForLoop(final JmlForLoop node, final P p) {
    final P tmpP = preVisit(node, p);
    final R r = scan(node.loopSpecs, tmpP);
    final R tmpR = super.visitForLoop(node, tmpP);
    return reduce(r, tmpR);
  }

  /**
   * Visiting JmlGroupName node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlGroupName(final JmlGroupName node, final P p) {
    final P tmpP = preVisit(node, p);
    final R r = scan(node.selection, tmpP);
    return r;
  }

  /**
   * Visiting Jml-import node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlImport(final JmlImport node, final P p) {
    final P tmpP = preVisit(node, p);
    final R r = super.visitImport(node, tmpP);
    return r;
  }

  /**
   * Visiting JmlLblExpression node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlLblExpression(final JmlLblExpression node, final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.expression, tmpP);
  }

  /**
   * Visiting jml method clause assignable node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlMethodClauseAssignable(final JmlMethodClauseStoreRef node,
                                          final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.list, tmpP);
  }

  /**
   * Visiting jml method clause conditional node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlMethodClauseConditional(
      final JmlMethodClauseConditional node,
      final P p) {
    final P tmpP = preVisit(node, p);
    final R r = scan(node.expression, tmpP);
    return scanAndReduce(node.predicate, tmpP, r);
  }

  /**
   * Visiting Jml method clause declaration node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlMethodClauseDecl(final JmlMethodClauseDecl node, final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.stats, tmpP);
  }

  /**
   * Visiting Jml method clause expression node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlMethodClauseExpr(final JmlMethodClauseExpr node, final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.expression, tmpP);
  }

  /**
   * Visiting jml method clause group node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlMethodClauseGroup(final JmlMethodClauseGroup node,
                                     final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.cases, tmpP);
  }

  /**
   * Visiting JmlMethodClauseSigOnly node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlMethodClauseSigOnly(final JmlMethodClauseSigOnly node,
                                       final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.list, tmpP);
  }

  /**
   * Visiting jml method clause signals node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlMethodClauseSignals(final JmlMethodClauseSignals node,
                                       final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.expression, tmpP);
  }

  /**
   * Visiting jml method declaration node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlMethodDecl(final JmlMethodDecl node, final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.cases, tmpP);
    return super.visitMethod(node, tmpP);
  }

  /**
   * Visiting jml method specification node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children
   */
  public R visitJmlMethodSpecs(final JmlMethodSpecs node, final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.cases, tmpP);
  }

  /**
   * Visiting jml primitive type node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return null
   */
  public R visitJmlPrimitiveTypeTree(final JmlPrimitiveTypeTree node,
                                     final P p) {
    return null;
  }

  /**
   * Visiting jml quantified expression node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children
   */
  public R visitJmlQuantifiedExpr(final JmlQuantifiedExpr node, final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.decls, tmpP);
    r = scanAndReduce(node.range, tmpP, r);
    return scanAndReduce(node.predicate, tmpP, r);
  }

  /**
   * Visiting jml refines node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return null
   */
  public R visitJmlRefines(final JmlRefines node, final P p) {
    return null;
  }

  /**
   * Visiting jml set comprehension node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children
   */
  public R visitJmlSetComprehension(final JmlSetComprehension node, final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.newtype, tmpP);
    r = scanAndReduce(node.variable, tmpP, r);
    return scanAndReduce(node.predicate, tmpP, r);
  }

  /**
   * Visiting jml singleton node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return null
   */
  public R visitJmlSingleton(final JmlSingleton node, final P p) {
    return null;
  }

  /**
   * Visiting jml specification case node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return just the result of corresponding method from the superclass.
   */
  public R visitJmlSpecificationCase(final JmlSpecificationCase node,
                                     final P p) {
    final P tmpP = preVisit(node, p);
    final R r = scan(node.clauses, tmpP);
    return scanAndReduce(node.modifiers, tmpP, r);
  }

  /**
   * Visiting jml statement node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children
   */
  public R visitJmlStatement(final JmlStatement node, final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.statement, tmpP);
  }

  /**
   * Visiting jml statement declarations node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children
   */
  public R visitJmlStatementDecls(final JmlStatementDecls node, final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.list, tmpP);
  }

  /**
   * Visiting jml statement expression node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlStatementExpr(final JmlStatementExpr node, final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.expression, tmpP);
    r = scanAndReduce(node.optionalExpression, tmpP, r);
    return r;
  }

  /**
   * Visiting jml statement loop node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children
   */
  public R visitJmlStatementLoop(final JmlStatementLoop node, final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.expression, tmpP);
  }

  /**
   * Visiting jml statement specification node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children
   */
  public R visitJmlStatementSpec(final JmlStatementSpec node, final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.statementSpecs, tmpP);
  }

  /**
   * Visiting JmlStoreRefArrayRange node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlStoreRefArrayRange(final JmlStoreRefArrayRange node,
                                      final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.expression, tmpP);
    r = scanAndReduce(node.lo, tmpP, r);
    r = scanAndReduce(node.hi, tmpP, r);
    return r;
  }

  /**
   * Visiting JmlStoreRefKeyword node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return null
   */
  public R visitJmlStoreRefKeyword(final JmlStoreRefKeyword node, final P p) {
    return null;
  }

  /**
   * Visiting JmlStoreRefListExpression node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlStoreRefListExpression(final JmlStoreRefListExpression node,
                                          final P p) {
    final P tmpP = preVisit(node, p);
    return scan(node.list, tmpP);
  }

  /**
   * Visiting jml type clause conditional node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlTypeClauseConditional(final JmlTypeClauseConditional node,
                                         final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.modifiers, tmpP);
    r = scanAndReduce(node.identifier, tmpP, r);
    return scanAndReduce(node.expression, tmpP, r);
  }

  /**
   * Visiting jml type clause constraint node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlTypeClauseConstraint(final JmlTypeClauseConstraint node,
                                        final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.modifiers, tmpP);
    r = scanAndReduce(node.expression, tmpP, r);
    r = scanAndReduce(node.sigs, tmpP, r);
    return r;
  }

  /**
   * Visiting jml type clause declaration node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlTypeClauseDecl(final JmlTypeClauseDecl node, final P p) {
    final P tmpP = preVisit(node, p);
    final R r = scan(node.modifiers, tmpP);
    return scanAndReduce(node.decl, tmpP, r);
  }

  /**
   * Visiting jml type clause expression node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlTypeClauseExpr(final JmlTypeClauseExpr node, final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.modifiers, tmpP);
    r = scanAndReduce(node.expression, tmpP, r);
    return r;

  }

  /**
   * Visiting jml clause "in" node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlTypeClauseIn(final JmlTypeClauseIn node, final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.modifiers, tmpP);
    r = scanAndReduce(node.list, tmpP, r);
    return r;

  }

  /**
   * Visiting jml type clause initializer node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlTypeClauseInitializer(final JmlTypeClauseInitializer node,
                                         final P p) {
    final P tmpP = preVisit(node, p);
    final R r = scan(node.modifiers, tmpP);
    return scanAndReduce(node.specs, tmpP, r);
  }

  /**
   * Visiting jml type clause maps node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlTypeClauseMaps(final JmlTypeClauseMaps node, final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.modifiers, tmpP);
    r = scanAndReduce(node.expression, tmpP, r);
    return scanAndReduce(node.list, tmpP, r);
  }

  /**
   * Visiting jml type clause monitors for node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlTypeClauseMonitorsFor(final JmlTypeClauseMonitorsFor node,
                                         final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.modifiers, tmpP);
    r = scanAndReduce(node.identifier, tmpP, r);
    return scanAndReduce(node.list, tmpP, r);
  }

  /**
   * Visiting jml type clause represents node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlTypeClauseRepresents(final JmlTypeClauseRepresents node,
                                        final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.modifiers, tmpP);
    r = scanAndReduce(node.ident, tmpP, r);
    return scanAndReduce(node.expression, tmpP, r);
  }

  /**
   * Visiting jml variable declaration node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlVariableDecl(final JmlVariableDecl node, final P p) {
    final P tmpP = preVisit(node, p);
    return super.visitVariable(node, tmpP);
  }

  /**
   * Visiting jml while loop node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlWhileLoop(final JmlWhileLoop node, final P p) {
    final P tmpP = preVisit(node, p);
    final R r = scan(node.loopSpecs, tmpP);
    final R tmpR = super.visitWhileLoop(node, tmpP);
    return reduce(r, tmpR);
  }

  /**
   * Visiting jml method invocation node.
   * @param node - node to visit.
   * @param p - additional data that might be useful while visiting the node.
   * @return result of visiting children.
   */
  public R visitJmlMethodInvocation(final JmlMethodInvocation node, final P p) {
    final P tmpP = preVisit(node, p);
    R r = scan(node.getTypeArguments(), tmpP);
    r = scanAndReduce(node.getMethodSelect(), tmpP, r);
    r = scanAndReduce(node.getArguments(), tmpP, r);    
    return r;
  }
}
