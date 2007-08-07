/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

import umbra.editor.ColorManager;
import umbra.editor.ColorValues;

/**
 * This method defines coloring rules in tags.
 * It has been generated automatically except obtaing
 * color values from the array in {@ref ColorValues}.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeTagScanner extends RuleBasedScanner {

  /**
   * TODO.
   */
  private static final int DOUBLE_QUOTE_RULE = 0;

  /**
   * TODO.
   */
  private static final int SINGLE_QUOTE_RULE = 1;

  /**
   * TODO.
   */
  private static final int LINE_RULE = 2;

  /**
   * TODO.
   */
  private static final int WHITESPACE_RULE = 3;

  /**
   * TODO.
   */
  private static final int NUMBER_OF_RULES = 4;

  /**
   * TODO.
   *
   * @param a_manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param a_mode the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   */
  public BytecodeTagScanner(final ColorManager a_manager, final int a_mode) {

    final IToken[] tokens = TokenGetter.getTokenTab(a_manager, a_mode);

    final WordRule linerule = new WordRule(new SpecialWordDetector());
    linerule.addWord("<init>", tokens[ColorValues.KEY]);

    final IRule[] rules = new IRule[NUMBER_OF_RULES];

    // Add rule for double quotes
    rules[DOUBLE_QUOTE_RULE] = new SingleLineRule("\"", "\"",
                                                  tokens[ColorValues.STRING],
                                                  '\\');
    // Add a rule for single quotes
    rules[SINGLE_QUOTE_RULE] = new SingleLineRule("'", "'",
                                                  tokens[ColorValues.STRING],
                                                  '\\');
    // Add generic whitespace rule.
    rules[LINE_RULE] = linerule;
    rules[WHITESPACE_RULE] = new WhitespaceRule(
                                              new BytecodeWhitespaceDetector());

    setRules(rules);
  }
}
