/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-21 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import jml2bml.exceptions.NotTranslatedRuntimeException;
import jml2bml.symbols.Symbols;
import annot.bcexpression.BCExpression;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;

import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;

/**
 * Utility class for translations.
 *
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
    final BCExpression bcExpr = expression.accept(RulesFactory
        .getExpressionRule(context), symb);
    if (JavaBasicType.JavaBool.compareTypes(bcExpr.getType1()) != JavaType.TYPES_EQUAL)
      throw new NotTranslatedRuntimeException(
        "assert expression must be boolean");
    return (AbstractFormula) bcExpr;
  }
}
