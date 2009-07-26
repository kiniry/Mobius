/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-21 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import javax.lang.model.type.TypeKind;

import jml2bml.exceptions.NotTranslatedRuntimeException;
import jml2bml.symbols.Symbols;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BooleanExpression;
import annot.bcexpression.formula.AbstractFormula;

import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;

/*
 * * Utility class for translations.
 * @author kjk (kjk@mimuw.edu.pl)
 * @version 0-0.1
 */
public final class TranslationUtil {
  /**
   * Hidden constructor.
   */
  private TranslationUtil() {

  }

  /**
   * Translates an expression to a BmlLib AbstractFormula.
   * @param expression expression to translate.
   * @param symb symbol table
   * @param context application context
   * @return formula for given expression
   * @throws NotTranslatedRuntimeException
   */
  public static AbstractFormula getFormula(final JCExpression expression,
                                           final Symbols symb,
                                           final Context context)
      throws NotTranslatedRuntimeException {
    if (expression == null)
      return null;
    final BCExpression expr = expression.accept(RulesFactory
        .getExpressionRule(context), symb);
    //in case invariant is an expression we have to convert it to a formula
    if (expr instanceof AbstractFormula) {
      return (AbstractFormula) expr;
    } else if (expression.type.getKind() == TypeKind.BOOLEAN) {
      return new BooleanExpression(expr);
    } else
      throw new NotTranslatedRuntimeException(
                                              "Cannot create formula from node:" +
                                                  expression);
  }
}
