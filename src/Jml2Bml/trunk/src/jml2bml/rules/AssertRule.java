/*
 * @title       "Jml2Bml"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2008-01-06 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import java.io.IOException;

import jml2bml.ast.AncestorFinder;
import jml2bml.bytecode.BytecodeUtil;

import org.apache.bcel.generic.InstructionHandle;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;

import annot.attributes.SingleAssert;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;

import com.sun.source.tree.MethodTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.util.Context;

/**
 * Rule for translating jml assert clauses. Uses ExpressionRule inside.
 * @author Jedrek
 * @author kjk
 *
 */
public class AssertRule extends TranslationRule<String, Void> {
  private final Context my_context;

  public AssertRule(final Context context) {
    this.my_context = context;
  }

  /**
   * visiting Jml statement expression. If this node represents "assert" clause,
   * generate the corresponding bml annotation. In other cases return null.
   * @param node - node to visit
   * @param p - additional data (not used)
   * @return bml-assert annotation or null.
   */
  public String visitJmlStatementExpr(final JmlStatementExpr node, final Void p) {
    if (node.token == JmlToken.ASSERT){
      final TranslationRule<BCExpression, Void> expressionRule = RulesFactory
          .getExpressionRule(my_context);
      AncestorFinder finder = my_context.get(AncestorFinder.class);
      BCClass clazz = my_context.get(BCClass.class);

      MethodTree method = (MethodTree) finder.getAncestor(node, Kind.METHOD);
      BCMethod bcMethod = BytecodeUtil.findMethod(method.getName(), clazz);
      if (node.expression != null) {
        BCExpression expression = node.expression.accept(expressionRule, p);
        System.out.println("Jestem");
        InstructionHandle ih1 = bcMethod.getBcelMethod().getInstructionList().getInstructionHandles()[0];
        SingleAssert ass = new SingleAssert(bcMethod, ih1, 1);
        bcMethod.addAttribute(ass);
        bcMethod.save();
      }
      try {
        clazz.saveToFile("Test.class");
      } catch (IOException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      if (node.optionalExpression != null){
//    	  BCExpression optionalExpression = node.optionalExpression.accept(expressionRule, p);
//      }
//      String optionalExpr = null;
//      if (node.optionalExpression != null) {
//        optionalExpr = node.optionalExpression.accept(expressionRule, p);
//      }
//      String ret = BmlKeywords.ASSERT + " ";
//      if (expr != null) {
//        ret += expr;
//      }
//      if (optionalExpr != null) {
//        ret += optionalExpr;
      }
//      return ret;
    return null;
  }

}
