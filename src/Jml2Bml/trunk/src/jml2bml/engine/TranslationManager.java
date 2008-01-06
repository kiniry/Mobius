package jml2bml.engine;

import java.util.Map;

import jml2bml.rules.NonNullRule;
import jml2bml.rules.RulesFactory;

import com.sun.source.tree.Tree;
import com.sun.tools.javac.util.Context;

/**
 * This class allows the user to register his own translation rules
 * @author Jedrek
 *
 */
public class TranslationManager {
	public static Jml2BmlTranslator getTranslator(Context context, Map<Tree, Tree> parents){
		Jml2BmlTranslator translator = new Jml2BmlTranslator(context);
		registerTranslationRules(translator, context);
		return translator;
	}

	/**
	 * In this method register all translation rules that should be used by the
	 * translator
	 * 
	 */
	private static void registerTranslationRules(Jml2BmlTranslator translator, Context context) {
		translator.registerTranslationRule(RulesFactory.getNonNullRule(context));
		translator.registerTranslationRule(RulesFactory.getExpressionRule(context));
		translator.registerTranslationRule(RulesFactory.getAssertRule(context));
	}
}
