/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.rules;

import jml2bml.ast.TreeNodeFinder;
import jml2bml.bytecode.BytecodeUtil;
import jml2bml.exceptions.NotTranslatedRuntimeException;
import jml2bml.symbols.Symbols;

import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.LineNumberGen;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;

import annot.attributes.method.SingleAssert;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcexpression.formula.AbstractFormula;

import com.sun.source.tree.LineMap;
import com.sun.source.tree.StatementTree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.util.Context;

/**
 * Rule for translating jml assert clauses. Uses ExpressionRule inside.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @author kjk    (kjk@mimuw.edu.pl)
 *
 * @version 0-0.1
 */
public class AssertRule extends TranslationRule < String, Symbols > {
  /**
   * Application context.
   */
  private final Context myContext;

  /**
   * Creates new instance of the AssertRule.
   * @param context application context
   */
  public AssertRule(final Context context) {
    super();
    this.myContext = context;
  }

  /**
   * visiting Jml statement expression. If this node represents "assert" clause,
   * generate the corresponding bml annotation. In other cases return null.
   * @param node - node to visit
   * @param symb - additional data (not used)
   * @return bml-assert annotation or null.
   * @throws NotTranslatedRuntimeException
   */
  @Override
  public String visitJmlStatementExpr(final JmlStatementExpr node,
                                      final Symbols symb)
    throws NotTranslatedRuntimeException {

    if (node.token == JmlToken.ASSERT) {
      final TreeNodeFinder finder = myContext.get(TreeNodeFinder.class);
      final BCClass clazz = symb.findClass();

      //Find an enclosing method
      final JmlMethodDecl method = (JmlMethodDecl) finder.getAncestor(node,
                                                                Kind.METHOD);
      final BCMethod bcMethod = BytecodeUtil.findMethod(method, clazz);

      if (node.expression != null) {
        final AbstractFormula form = TranslationUtil
            .getFormula(node.expression, symb, myContext);

        final StatementTree targetStmt = findFirstNotEmptySibling(finder, node);
        System.out.println("Assertion: " + form +
                           " should be added to statement: " + targetStmt);
        final InstructionHandle targetIH = translateStatement(targetStmt,
                                                              bcMethod);
        final int count = bcMethod.getAmap().getAllAt(targetIH).size();
        bcMethod
            .addAttribute(new SingleAssert(bcMethod, targetIH, count, form));
      }
      //TODO: what with node.optionalExpression??
    }
    return null;
  }

  /**
   * Checks if given statement is instance of JmlAbstractStatement.
   * @param stmt statement to check
   * @return if the given statement is a Jml statement
   */
  private static boolean isJmlStatement(final StatementTree stmt) {
    return (stmt instanceof JmlAbstractStatement);
  }

  /**
   * Finds first sibling of stmt that is not empty.
   * @param finder util to find ancestors
   * @param stmt statement, for which the sibling should be found
   * @return found sibling
   */
  private static StatementTree findFirstNotEmptySibling(
      final TreeNodeFinder finder,
      final StatementTree stmt) {
    StatementTree tmp = stmt;
    do {
      tmp = (StatementTree) finder.getNextSibling(tmp);
    } while (tmp != null && isJmlStatement(tmp));
    return tmp;
  }

  private InstructionHandle translateStatement(final StatementTree stmt,
                                               final BCMethod method)
    throws NotTranslatedRuntimeException {
    if (stmt == null) {
      return method.getInstructions().getEnd();
    } else {
      final LineMap lineMap = myContext.get(LineMap.class);
      final long sourceLine = BytecodeUtil.getLineNumber(stmt, lineMap);
      for (LineNumberGen lng : method.getBcelMethod().getLineNumbers()) {
        //FIXME: can one source line have more than one line number in output??
        if (sourceLine == lng.getSourceLine())
          return lng.getInstruction();
      }
    }
    throw new NotTranslatedRuntimeException(
      "Error with finding target instruction in bytecode");
  }
}
