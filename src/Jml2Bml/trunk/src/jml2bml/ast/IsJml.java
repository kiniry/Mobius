/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-02-09 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.ast;

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
public class IsJml implements TreeVisitor<Boolean, Void>,
    JmlTreeVisitor<Boolean, Void> {

  public Boolean visitAnnotation(AnnotationTree node, Void p) {
    return false;
  }

  public Boolean visitArrayAccess(ArrayAccessTree node, Void p) {
    return false;
  }

  public Boolean visitArrayType(ArrayTypeTree node, Void p) {
    return false;
  }

  public Boolean visitAssert(AssertTree node, Void p) {
    return false;
  }

  public Boolean visitAssignment(AssignmentTree node, Void p) {
    return false;
  }

  public Boolean visitBinary(BinaryTree node, Void p) {
    return false;
  }

  public Boolean visitBlock(BlockTree node, Void p) {
    return false;
  }

  public Boolean visitBreak(BreakTree node, Void p) {
    return false;
  }

  public Boolean visitCase(CaseTree node, Void p) {
    return false;
  }

  public Boolean visitCatch(CatchTree node, Void p) {
    return false;
  }

  public Boolean visitClass(ClassTree node, Void p) {
    return false;
  }

  public Boolean visitCompilationUnit(CompilationUnitTree node, Void p) {
    return false;
  }

  public Boolean visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
    return false;
  }

  public Boolean visitConditionalExpression(ConditionalExpressionTree node,
                                            Void p) {
    return false;
  }

  public Boolean visitContinue(ContinueTree node, Void p) {
    return false;
  }

  public Boolean visitDoWhileLoop(DoWhileLoopTree node, Void p) {
    return false;
  }

  public Boolean visitEmptyStatement(EmptyStatementTree node, Void p) {
    return false;
  }

  public Boolean visitEnhancedForLoop(EnhancedForLoopTree node, Void p) {
    return false;
  }

  public Boolean visitErroneous(ErroneousTree node, Void p) {
    return false;
  }

  public Boolean visitExpressionStatement(ExpressionStatementTree node, Void p) {
    return false;
  }

  public Boolean visitForLoop(ForLoopTree node, Void p) {
    return false;
  }

  public Boolean visitIdentifier(IdentifierTree node, Void p) {
    return false;
  }

  public Boolean visitIf(IfTree node, Void p) {
    return false;
  }

  public Boolean visitImport(ImportTree node, Void p) {
    return false;
  }

  public Boolean visitInstanceOf(InstanceOfTree node, Void p) {
    return false;
  }

  public Boolean visitLabeledStatement(LabeledStatementTree node, Void p) {
    return false;
  }

  public Boolean visitLiteral(LiteralTree node, Void p) {
    return false;
  }

  public Boolean visitMemberSelect(MemberSelectTree node, Void p) {
    return false;
  }

  public Boolean visitMethod(MethodTree node, Void p) {
    return false;
  }

  public Boolean visitMethodInvocation(MethodInvocationTree node, Void p) {
    return false;
  }

  public Boolean visitModifiers(ModifiersTree node, Void p) {
    return false;
  }

  public Boolean visitNewArray(NewArrayTree node, Void p) {
    return false;
  }

  public Boolean visitNewClass(NewClassTree node, Void p) {
    return false;
  }

  public Boolean visitOther(Tree node, Void p) {
    return false;
  }

  public Boolean visitParameterizedType(ParameterizedTypeTree node, Void p) {
    return false;
  }

  public Boolean visitParenthesized(ParenthesizedTree node, Void p) {
    return false;
  }

  public Boolean visitPrimitiveType(PrimitiveTypeTree node, Void p) {
    return false;
  }

  public Boolean visitReturn(ReturnTree node, Void p) {
    return false;
  }

  public Boolean visitSwitch(SwitchTree node, Void p) {
    return false;
  }

  public Boolean visitSynchronized(SynchronizedTree node, Void p) {
    return false;
  }

  public Boolean visitThrow(ThrowTree node, Void p) {
    return false;
  }

  public Boolean visitTry(TryTree node, Void p) {
    return false;
  }

  public Boolean visitTypeCast(TypeCastTree node, Void p) {
    return false;
  }

  public Boolean visitTypeParameter(TypeParameterTree node, Void p) {
    return false;
  }

  public Boolean visitUnary(UnaryTree node, Void p) {
    return false;
  }

  public Boolean visitVariable(VariableTree node, Void p) {
    return false;
  }

  public Boolean visitWhileLoop(WhileLoopTree node, Void p) {
    return false;
  }

  public Boolean visitWildcard(WildcardTree node, Void p) {
    return false;
  }

  public Boolean visitJmlBinary(JmlBinary arg0, Void arg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlClassDecl(JmlClassDecl arg0, Void arg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlCompilationUnit(JmlCompilationUnit arg0, Void arg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlDoWhileLoop(JmlDoWhileLoop arg0, Void arg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlEnhancedForLoop(JmlEnhancedForLoop arg0, Void arg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlForLoop(JmlForLoop arg0, Void arg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlFunction(JmlFunction arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlGroupName(JmlGroupName arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlImport(JmlImport arg0, Void arg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlLblExpression(JmlLblExpression arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseAssignable(JmlMethodClauseAssignable arg0,
                                                Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseConditional(
                                                 JmlMethodClauseConditional arg0,
                                                 Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseDecl(JmlMethodClauseDecl arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseExpr(JmlMethodClauseExpr arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseGroup(JmlMethodClauseGroup arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly arg0,
                                             Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodClauseSignals(JmlMethodClauseSignals arg0,
                                             Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlMethodDecl(JmlMethodDecl arg0, Void arg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlMethodSpecs(JmlMethodSpecs arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlQuantifiedExpr(JmlQuantifiedExpr arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlRefines(JmlRefines arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlSetComprehension(JmlSetComprehension arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlSingleton(JmlSingleton arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlSpecificationCase(JmlSpecificationCase arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStatement(JmlStatement arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStatementDecls(JmlStatementDecls arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStatementExpr(JmlStatementExpr arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStatementLoop(JmlStatementLoop arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStatementSpec(JmlStatementSpec arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStoreRefArrayRange(JmlStoreRefArrayRange arg0,
                                            Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStoreRefKeyword(JmlStoreRefKeyword arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlStoreRefListExpression(JmlStoreRefListExpression arg0,
                                                Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseConditional(JmlTypeClauseConditional arg0,
                                               Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseConstraint(JmlTypeClauseConstraint arg0,
                                              Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseDecl(JmlTypeClauseDecl arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseExpr(JmlTypeClauseExpr arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseIn(JmlTypeClauseIn arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseInitializer(JmlTypeClauseInitializer arg0,
                                               Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseMaps(JmlTypeClauseMaps arg0, Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor arg0,
                                               Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlTypeClauseRepresents(JmlTypeClauseRepresents arg0,
                                              Void arg1) {
    // TODO Auto-generated method stub
    return true;
  }

  public Boolean visitJmlVariableDecl(JmlVariableDecl arg0, Void arg1) {
    // TODO Auto-generated method stub
    return false;
  }

  public Boolean visitJmlWhileLoop(JmlWhileLoop arg0, Void arg1) {
    // TODO Auto-generated method stub
    return false;
  }

}
