/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-02-09 University of Warsaw" @license "All rights reserved. This program
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
import com.sun.source.tree.TreeVisitor;
import com.sun.source.tree.TryTree;
import com.sun.source.tree.TypeCastTree;
import com.sun.source.tree.TypeParameterTree;
import com.sun.source.tree.UnaryTree;
import com.sun.source.tree.VariableTree;
import com.sun.source.tree.WhileLoopTree;
import com.sun.source.tree.WildcardTree;

/**
 * This is a class that helps to ifentify if objects are Jml objects.
 *
 * @author kjk (kjk@mimuw.edu.pl)
 */
public class IsJml implements TreeVisitor < Boolean, Void >,
    JmlTreeVisitor < Boolean, Void > {

  public Boolean visitAnnotation(final AnnotationTree node, final Void p) {
    return false;
  }

  public Boolean visitArrayAccess(final ArrayAccessTree node, final Void p) {
    return false;
  }

  public Boolean visitArrayType(final ArrayTypeTree node, final Void p) {
    return false;
  }

  public Boolean visitAssert(final AssertTree node, final Void p) {
    return false;
  }

  public Boolean visitAssignment(final AssignmentTree node, final Void p) {
    return false;
  }

  public Boolean visitBinary(final BinaryTree node, final Void p) {
    return false;
  }

  public Boolean visitBlock(final BlockTree node, final Void p) {
    return false;
  }

  public Boolean visitBreak(final BreakTree node, final Void p) {
    return false;
  }

  public Boolean visitCase(final CaseTree node, final Void p) {
    return false;
  }

  public Boolean visitCatch(final CatchTree node, final Void p) {
    return false;
  }

  public Boolean visitClass(final ClassTree node, final Void p) {
    return false;
  }

  public Boolean visitCompilationUnit(final CompilationUnitTree node,
                                      final Void p) {
    return false;
  }

  public Boolean visitCompoundAssignment(final CompoundAssignmentTree node,
                                         final Void p) {
    return false;
  }

  public Boolean visitConditionalExpression(
      final ConditionalExpressionTree node,
      final Void p) {
    return false;
  }

  public Boolean visitContinue(final ContinueTree node, final Void p) {
    return false;
  }

  public Boolean visitDoWhileLoop(final DoWhileLoopTree node, final Void p) {
    return false;
  }

  public Boolean visitEmptyStatement(final EmptyStatementTree node,
                                     final Void p) {
    return false;
  }

  public Boolean visitEnhancedForLoop(final EnhancedForLoopTree node,
                                      final Void p) {
    return false;
  }

  public Boolean visitErroneous(final ErroneousTree node, final Void p) {
    return false;
  }

  public Boolean visitExpressionStatement(final ExpressionStatementTree node,
                                          final Void p) {
    return false;
  }

  public Boolean visitForLoop(final ForLoopTree node, final Void p) {
    return false;
  }

  public Boolean visitIdentifier(final IdentifierTree node, final Void p) {
    return false;
  }

  public Boolean visitIf(final IfTree node, final Void p) {
    return false;
  }

  public Boolean visitImport(final ImportTree node, final Void p) {
    return false;
  }

  public Boolean visitInstanceOf(final InstanceOfTree node, final Void p) {
    return false;
  }

  public Boolean visitLabeledStatement(final LabeledStatementTree node,
                                       final Void p) {
    return false;
  }

  public Boolean visitLiteral(final LiteralTree node, final Void p) {
    return false;
  }

  public Boolean visitMemberSelect(final MemberSelectTree node, final Void p) {
    return false;
  }

  public Boolean visitMethod(final MethodTree node, final Void p) {
    return false;
  }

  public Boolean visitMethodInvocation(final MethodInvocationTree node,
                                       final Void p) {
    return false;
  }

  public Boolean visitModifiers(final ModifiersTree node, final Void p) {
    return false;
  }

  public Boolean visitNewArray(final NewArrayTree node, final Void p) {
    return false;
  }

  public Boolean visitNewClass(final NewClassTree node, final Void p) {
    return false;
  }

  public Boolean visitOther(final Tree node, final Void p) {
    return false;
  }

  public Boolean visitParameterizedType(final ParameterizedTypeTree node,
                                        final Void p) {
    return false;
  }

  public Boolean visitParenthesized(final ParenthesizedTree node,
                                    final Void p) {
    return false;
  }

  public Boolean visitPrimitiveType(final PrimitiveTypeTree node,
                                    final Void p) {
    return false;
  }

  public Boolean visitReturn(final ReturnTree node, final Void p) {
    return false;
  }

  public Boolean visitSwitch(final SwitchTree node, final Void p) {
    return false;
  }

  public Boolean visitSynchronized(final SynchronizedTree node, final Void p) {
    return false;
  }

  public Boolean visitThrow(final ThrowTree node, final Void p) {
    return false;
  }

  public Boolean visitTry(final TryTree node, final Void p) {
    return false;
  }

  public Boolean visitTypeCast(final TypeCastTree node, final Void p) {
    return false;
  }

  public Boolean visitTypeParameter(final TypeParameterTree node,
                                    final Void p) {
    return false;
  }

  public Boolean visitUnary(final UnaryTree node, final Void p) {
    return false;
  }

  public Boolean visitVariable(final VariableTree node, final Void p) {
    return false;
  }

  public Boolean visitWhileLoop(final WhileLoopTree node, final Void p) {
    return false;
  }

  public Boolean visitWildcard(final WildcardTree node, final Void p) {
    return false;
  }

  public Boolean visitJmlBinary(final JmlBinary anArg0, final Void anArg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlClassDecl(final JmlClassDecl anArg0,
                                   final Void anArg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlCompilationUnit(final JmlCompilationUnit anArg0,
                                         final Void anArg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlDoWhileLoop(final JmlDoWhileLoop anArg0,
                                     final Void anArg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlEnhancedForLoop(final JmlEnhancedForLoop anArg0,
                                         final Void anArg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlForLoop(final JmlForLoop anArg0, final Void anArg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlGroupName(final JmlGroupName anArg0,
                                   final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlImport(final JmlImport anArg0, final Void anArg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlLblExpression(final JmlLblExpression anArg0,
                                       final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseAssignable(
      final JmlMethodClauseStoreRef anArg0,
      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseConditional(
      final JmlMethodClauseConditional anArg0,
      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseDecl(final JmlMethodClauseDecl anArg0,
                                          final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseExpr(final JmlMethodClauseExpr anArg0,
                                          final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseGroup(final JmlMethodClauseGroup anArg0,
                                           final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseSigOnly(
      final JmlMethodClauseSigOnly anArg0,
      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseSignals(
      final JmlMethodClauseSignals anArg0,
      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodDecl(final JmlMethodDecl anArg0,
                                    final Void anArg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlMethodSpecs(final JmlMethodSpecs anArg0,
                                     final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlPrimitiveTypeTree(final JmlPrimitiveTypeTree anArg0,
                                           final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlQuantifiedExpr(final JmlQuantifiedExpr anArg0,
                                        final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlRefines(final JmlRefines anArg0, final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlSetComprehension(final JmlSetComprehension anArg0,
                                          final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlSingleton(final JmlSingleton anArg0,
                                   final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlSpecificationCase(final JmlSpecificationCase anArg0,
                                           final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStatement(final JmlStatement anArg0,
                                   final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStatementDecls(final JmlStatementDecls anArg0,
                                        final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStatementExpr(final JmlStatementExpr anArg0,
                                       final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStatementLoop(final JmlStatementLoop anArg0,
                                       final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStatementSpec(final JmlStatementSpec anArg0,
                                       final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStoreRefArrayRange(final JmlStoreRefArrayRange anArg0,
                                            final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStoreRefKeyword(final JmlStoreRefKeyword anArg0,
                                         final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStoreRefListExpression(
      final JmlStoreRefListExpression anArg0,
      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseConditional(
      final JmlTypeClauseConditional anArg0,
      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseConstraint(
      final JmlTypeClauseConstraint anArg0,
      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseDecl(final JmlTypeClauseDecl anArg0,
                                        final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseExpr(final JmlTypeClauseExpr anArg0,
                                        final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseIn(final JmlTypeClauseIn anArg0,
                                      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseInitializer(
      final JmlTypeClauseInitializer anArg0,
      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseMaps(final JmlTypeClauseMaps anArg0,
                                        final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseMonitorsFor(
      final JmlTypeClauseMonitorsFor anArg0,
      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseRepresents(
      final JmlTypeClauseRepresents anArg0,
      final Void anArg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlVariableDecl(final JmlVariableDecl anArg0,
                                      final Void anArg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlWhileLoop(final JmlWhileLoop anArg0,
                                   final Void anArg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlMethodInvocation(JmlMethodInvocation that, Void p) {
    // TODO Auto-generated method stub
    return true;
  }

}
