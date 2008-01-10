/*
 * @title       "Jml2Bml"
 * @description ""JML to BML Compiler"
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
import org.apache.bcel.generic.LineNumberGen;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;

import annot.attributes.SingleAssert;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.BCExpression;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.javatype.JavaBasicType;

import com.sun.source.tree.LineMap;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.StatementTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.tree.JCTree;
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

    if (node.token == JmlToken.ASSERT) {
      final TreeNodeFinder finder = my_context.get(TreeNodeFinder.class);
      final BCClass clazz = my_context.get(BCClass.class);

      //Find an enclosing method
      final MethodTree method = (MethodTree) finder.getAncestor(node, Kind.METHOD);
      final BCMethod bcMethod = BytecodeUtil.findMethod(method.getName(), clazz);

      if (node.expression != null) {
        final BCExpression expression = node.expression.accept(RulesFactory
                                                               .getExpressionRule(my_context),
                                                               p);
        if (expression.getType1() != JavaBasicType.JavaBool)
          throw new NotTranslatedException("assert expression must be boolean");
        final AbstractFormula form = (AbstractFormula) expression;

        final StatementTree targetStmt = findFirstNotEmptySibling(finder, node);
        System.out.println("Assertion: "+form+" should be added to statement: "+targetStmt);
        final InstructionHandle targetIH = translateStatement(targetStmt,
                                                              bcMethod);
        final int count = bcMethod.getAmap().getAllAt(targetIH).size();
        bcMethod.addAttribute(new SingleAssert(bcMethod, targetIH,
                                               count, form));
      }
      //TODO: what with node.optionalExpression??
    }
    return null;
  }

  private static boolean isJmlStatement(final StatementTree stmt) {
    return (stmt instanceof JmlAbstractStatement);
  }

  private static StatementTree findFirstNotEmptySibling(final TreeNodeFinder finder,
                                                        StatementTree stmt) {
    do {
      stmt = finder.getNextStatement(stmt);
    } while(stmt != null && isJmlStatement(stmt));
    return stmt;
  }

  public InstructionHandle translateStatement(final StatementTree stmt,
                                              final BCMethod method) {
    if (stmt == null) {
      return method.getInstructions().getEnd();
    } else {
      final LineMap lineMap = my_context.get(LineMap.class);
      final JCTree jctree = (JCTree) stmt;
      final long sourceLine = lineMap.getLineNumber(jctree.getStartPosition());
      for (LineNumberGen lng : method.getBcelMethod().getLineNumbers()) {
        //FIXME: can one source line have more than one line number in output??
        if (sourceLine == lng.getSourceLine())
          return lng.getInstruction();
      }
    }
    throw new NotTranslatedException("Error with finding target instruction in bytecode");
  }
}
