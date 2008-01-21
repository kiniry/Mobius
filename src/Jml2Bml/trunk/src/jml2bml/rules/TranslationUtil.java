/*
 * @title       "Jml2Bml"
 * @description ""JML to BML Compiler"
 * @copyright   "(c) 2008-01-21 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.rules;

import jml2bml.exceptions.NotTranslatedException;
import jml2bml.symbols.Symbols;
import annot.bcexpression.BCExpression;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.javatype.JavaBasicType;

import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;

/**
 * Utility class for translations.
 *
 * @author kjk (kjk@mimuw.edu.pl)
 * @version 0-0.1
 */
public class TranslationUtil {

  public static AbstractFormula getFormula(JCExpression expression,
                                           Symbols symb, Context context) {
    if (expression == null)
      return null;
    final BCExpression bcExpr = expression.accept(RulesFactory
        .getExpressionRule(context), symb);
    if (bcExpr.getType1() != JavaBasicType.JavaBool)
      throw new NotTranslatedException("assert expression must be boolean");
    return (AbstractFormula) bcExpr;
  }
}
