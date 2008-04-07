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
 * This class is responsible for colouring these texts in a byte code
 * editor window which are inside BML annotations areas. This class uses
 * special 4 rules which describe the way the different sequences are coloured.
 * Colours are chosen as a token array with a particular colouring
 * style given in the constructor.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeTagScanner extends RuleBasedScanner {

  /**
   * The number of the rule that handles the recognition of the areas between
   * the double quote characters.
   */
  private static final int DOUBLE_QUOTE_RULE = 0;

  /**
   * The number of the rule that handles the recognition of the areas between
   * the single quote characters.
   */
  private static final int SINGLE_QUOTE_RULE = 1;

  /**
   * The number of the rule that handles the recognition of the whitespace
   * areas.
   */
  private static final int WHITESPACE_RULE = 2;

  /**
   * The number of the rule that handles the colouring of the BML keywords.
   */
  private static final int KEYWORD_RULE = 3;

  /**
   * The number of colouring rules used in this class.
   */
  private static final int NUMBER_OF_RULES = 4;

  /**
   * The constructor initialises the scanning rules for the current scanner.
   * It associates the given colour manager and colouring mode with the
   * 
   *
   * @param a_manager the colour manager related to the current byte code
   *    editor, it must be the same as in the current
   *    {@link umbra.editor.BytecodeConfiguration} object
   * @param a_mode the number of the current colouring style, it must be the
   *    same as in the current {@link umbra.editor.BytecodeConfiguration} object
   */
  public BytecodeTagScanner(final ColorManager a_manager, final int a_mode) {

    final IToken[] tokens = TokenGetter.getTokenTab(a_manager, a_mode);

    final IRule[] rules = new IRule[NUMBER_OF_RULES];

    // Add rule for double quotes
    rules[DOUBLE_QUOTE_RULE] = new SingleLineRule("\"", "\"",
                                                  tokens[ColorValues.STRING],
                                                  '\\');
    // Add a rule for single quotes
    rules[SINGLE_QUOTE_RULE] = new SingleLineRule("'", "'",
                                                  tokens[ColorValues.STRING],
                                                  '\\');
    rules[WHITESPACE_RULE] = new WhitespaceRule(
                                              new BytecodeWhitespaceDetector());
    rules[KEYWORD_RULE] = createKeywordRule(tokens);

    setRules(rules);
  }

  private IRule createKeywordRule(final IToken[] the_tokens) {
    final WordRule insrule = new WordRule(new BytecodeWordDetector(),
                                          the_tokens[ColorValues.ANNOT]);
    for (int i = 0; i < BytecodeStrings.BML_KEYWORDS.length; i++) {
      insrule.addWord(BytecodeStrings.BML_KEYWORDS[i],
              the_tokens[ColorValues.ANNOTKEY]);
    }
    return insrule;
  }
}
