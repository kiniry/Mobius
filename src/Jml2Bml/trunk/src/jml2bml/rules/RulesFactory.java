/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.rules;

import jml2bml.symbols.Symbols;
import annot.bcexpression.BCExpression;

import com.sun.tools.javac.util.Context;

/**
 * Rules factory. If you implement your own rule, a good idea is to add
 * appropriate method to this factory.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0.0-1
 */
public final class RulesFactory {
  /**
   * Hidden constructor.
   */
  private RulesFactory() {

  }

  /**
   * Returns an instance of ExpressionRule (responsible for translating
   * JML expressions to BML expressions).
   * @param context application context
   * @return instance of ExpressionRule
   */
  public static TranslationRule < BCExpression, Symbols > getExpressionRule(
      final Context context) {
    return new ExpressionRule(context);
  }

  /**
   * Returns an instance of AssertRule.
   * @param context application context
   * @return instance of assert rule
   */
  public static TranslationRule < String, Symbols > getAssertRule(
      final Context context) {
    return new AssertRule(context);
  }

  /**
   * Creates an instance of specification case rule.
   * @param context application context
   * @return instance of specification case rule.
   */
  public static TranslationRule < String, Symbols > getSpecificationCaseRule(
      final Context context) {
    return new SpecificationCaseRule(context);
  }

  /**
   * Creates an instance of TypeClauseExprRule.
   *
   * @param context application context
   * @return created rule
   */
  public static TranslationRule < String, Symbols > getTypeClauseExprRule(
      final Context context) {
    return new TypeClauseExprRule(context);
  }

  /**
   * Creates an instance of rule responsible for translating loop invariants.
   * @param context application context
   * @return loop invariant rule
   */
  public static TranslationRule < String, Symbols > getLoopInvariantRule(
      final Context context) {
    return new LoopInvariantRule(context);
  }
}
