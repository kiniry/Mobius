package jml2bml.rules;

import jml2bml.engine.Symbols;
import annot.bcexpression.BCExpression;

import com.sun.tools.javac.util.Context;

/**
 * Rules factory. If you implement your own rule, a good idea is to add
 * appropriate method to this factory.
 * 
 * @author Jedrek
 * 
 */
public class RulesFactory {
  /**
   * Returns an instance of ExpressionRule
   */
  public static TranslationRule<BCExpression, Symbols> getExpressionRule(Context context) {
    return new ExpressionRule(context);
  }

  /**
   * Returns an instance of AssertRule
   */
  public static TranslationRule<String, Symbols> getAssertRule(Context context) {
    return new AssertRule(context);
  }

  public static TranslationRule<String, Symbols> getEnsuresRule(Context context) {
    return new RequiresRule(context);
  }
}
