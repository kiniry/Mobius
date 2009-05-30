/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.WordRule;

import umbra.lib.BytecodeStrings;

/**
 * This class is responsible for colouring these texts in a byte code
 * editor window which are inside constant pool areas. This class uses
 * special 4 rules which describe the way the different sequences are coloured.
 * Colours are chosen as a token array with a particular colouring
 * style given in the constructor.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeCPSecScanner extends RuleBasedScanner {

  /**
   * The number of the rule that handles the colouring of the constant pool
   * keywords.
   */
  private static final int KEYWORD_RULE = 0;

  /**
   * The number of colouring rules used in this class.
   */
  private static final int NUMBER_OF_RULES = 1;

  /**
   * The constructor initialises the scanning rules for the current scanner.
   * It creates and the scanning rules taking into account the given colour
   * manager and colouring mode. It creates the rules to recognise constant
   * pool keywords.
   *
   * @param the_manager the colour manager related to the current byte code
   *    editor, it must be the same as in the current
   *    {@link umbra.editor.BytecodeConfiguration} object
   * @param a_mode the number of the current colouring style, it must be the
   *    same as in the current {@link umbra.editor.BytecodeConfiguration} object
   */
  public BytecodeCPSecScanner(final ColorManager the_manager,
                              final int a_mode) {
    final IToken[] tokens = TokenGetter.getTokenTab(the_manager, a_mode);
    final IRule[] rules = new IRule[NUMBER_OF_RULES];

    // Add rule for const keyword
    rules[KEYWORD_RULE] = createKeywordRule(
      tokens[ColorValues.SLOT_BMLKEYWORDS]);
    setRules(rules);
  }

  /**
   * This method creates a {@link WordRule} object which recognises all the
   * constant pool keywords. It and assigns to them the given colour token.
   *
   * @param a_token the token to assign to the returned word rule
   * @return the scanning rule that recognises the constant pool keywords
   */
  private IRule createKeywordRule(final IToken a_token) {
    final WordRule insrule = new WordRule(new BytecodeWordDetector(), a_token);
    for (int i = 0; i < BytecodeStrings.CP_KEYWORDS.length; i++) {
      insrule.addWord(BytecodeStrings.CP_KEYWORDS[i], a_token);
    }
    return insrule;
  }
}
