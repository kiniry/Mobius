/*
 * @title       "Jml2Bml"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2008-01-06 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import jml2bml.ast.TreeNodeFinder;
import jml2bml.bytecode.BytecodeUtil;
import jml2bml.bytecode.ClassFileLocation;
import jml2bml.engine.JmlTokens;
import jml2bml.engine.Symbols;
import jml2bml.exceptions.NotTranslatedException;

import org.apache.bcel.generic.InstructionHandle;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;

import annot.attributes.SingleAssert;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.javatype.JavaBasicType;

import com.sun.source.tree.MethodTree;
import com.sun.source.tree.StatementTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.util.Context;

/**
 * Rule for translating jml assert clauses. Uses ExpressionRule inside.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @author kjk    (kjk@mimuw.edu.pl)
 *
 */
public class AssertRule extends TranslationRule<String, Symbols> {
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
  public String visitJmlStatementExpr(final JmlStatementExpr node,
                                      final Symbols p) {

    final String token = node.token.internedName();
    if (JmlTokens.ASSERT.equals(token)) {
      final TranslationRule<BCExpression, Symbols> expressionRule = RulesFactory
          .getExpressionRule(my_context);

      BCExpression expr;
      TreeNodeFinder finder = my_context.get(TreeNodeFinder.class);
      BCClass clazz = my_context.get(BCClass.class);
      ClassFileLocation classLoc = my_context.get(ClassFileLocation.class);

      //Find an enclosing method
      MethodTree method = (MethodTree) finder.getAncestor(node, Kind.METHOD);
      BCMethod bcMethod = BytecodeUtil.findMethod(method.getName(), clazz);
      
      //Find statement the assert applies to
      StatementTree stmt = findFirstNotEmptySibling(finder, node);
      if (node.expression != null) {
        final BCExpression expression = node.expression.accept(expressionRule,
                                                               p);
        if (expression.getType1() != JavaBasicType.JavaBool)
          throw new NotTranslatedException("assert expression must be boolean");
        final AbstractFormula form = (AbstractFormula) expression;
        System.out.println("Assertion: "+form+" should be added to statement: "+stmt);
        //insert as the last assertion in first instruction
        InstructionHandle ih1 = bcMethod.getBcelMethod().getInstructionList()
            .getInstructionHandles()[0];
        int count = bcMethod.getAmap().getAllAt(ih1).size();
        SingleAssert ass = new SingleAssert(bcMethod, ih1, count, form);
        bcMethod.addAttribute(ass);
      }
    }
    return null;
  }
  
  private static boolean isJmlStatement(StatementTree stmt){
    return (stmt instanceof JmlAbstractStatement);
  }
  
  private static StatementTree findFirstNotEmptySibling(TreeNodeFinder finder, StatementTree stmt){
    do {
      stmt = finder.getNextStatement(stmt);
    } while(stmt != null || isJmlStatement(stmt));
    return stmt;
  }
}
