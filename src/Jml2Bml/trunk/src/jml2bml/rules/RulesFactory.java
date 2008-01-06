package jml2bml.rules;

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
	public static TranslationRule getExpressionRule(Context context) {
		return new ExpressionRule(context);
	}
	/**
	 * Returns an instance of NonNullRule
	 */
	public static TranslationRule getNonNullRule(Context context) {
		return new NonNullRule(context);
	}
	/**
	 * Returns an instance of AssertRule
	 */
	public static TranslationRule getAssertRule(Context context) {
		return new AssertRule(context);
	}
}
