/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-06 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.engine;

import jml2bml.rules.ModifiersRule;
import jml2bml.rules.RulesFactory;

import com.sun.tools.javac.util.Context;

/**
 * This class allows the user to register his own translation rules.
 * @author Jedrek (fulara@mimuw.edu.pl)
 * @version 0.0-1
 */
public final class TranslationManager {
  /**
   * Hidden constructor.
   */
  private TranslationManager() {

  }

  /**
   * Creates an instance of the Jml2BmlTranslator.
   * @param context application context
   * @return translator, with all rules registered.
   */
  public static Jml2BmlTranslator getTranslator(final Context context) {
    final Jml2BmlTranslator translator = new Jml2BmlTranslator(context);
    registerTranslationRules(translator, context);
    return translator;
  }

  /**
   * In this method register all translation rules that should be used by the
   * translator.
   * @param translator
   * @param context application context
   */
  private static void registerTranslationRules(
      final Jml2BmlTranslator translator,
      final Context context) {
    translator.registerTranslationRule(RulesFactory.getAssertRule(context));
    translator.registerTranslationRule(RulesFactory
        .getSpecificationCaseRule(context));
    translator.registerTranslationRule(RulesFactory
        .getTypeClauseExprRule(context));
    translator.registerTranslationRule(RulesFactory
        .getLoopInvariantRule(context));
    translator.registerTranslationRule(new ModifiersRule(context));
  }
}
