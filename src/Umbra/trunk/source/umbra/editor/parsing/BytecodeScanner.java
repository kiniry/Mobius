/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.NumberRule;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

import umbra.editor.ColorManager;
import umbra.editor.ColorValues;


/**
 * This class is responsible for coloring all text in a bytecode
 * editor window according to some special 9 rules.
 * Colors are chosen as a token array with a particular colouring style
 * given in the constructor.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeScanner extends RuleBasedScanner {

  /**
   * TODO.
   */
  private static final int RULE_EOL = 0;

  /**
   * TODO.
   */
  private static final int RULE_INSTRUCTION = 1;

  /**
   * TODO.
   */
  private static final int RULE_SEPARATOR = 2;
  /**
   * TODO.
   */
  private static final int RULE_HASH = 3;
  /**
   * TODO.
   */
  private static final int RULE_PERCENT = 4;
  /**
   * TODO.
   */
  private static final int RULE_PARENTHESES = 5;
  /**
   * TODO.
   */
  private static final int RULE_BRACES = 6;
  /**
   * TODO.
   */
  private static final int RULE_NUMBER = 7;
  /**
   * TODO.
   */
  private static final int RULE_WHITESPACE = 8;
  /**
   * TODO.
   */
  private static final int RULE_STAR = 9;
  /**
   * TODO.
   */
  private static final int RULE_COMMENT = 10;

  /**
   * TODO.
   */
  private static final int NUMBER_OF_RULES = 11;


  /**
   * This method TODO
   * sets the scanning rules.
   *
   *
   * @param the_manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param a_mode the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   */
  public BytecodeScanner(final ColorManager the_manager, final int a_mode) {

    final IToken[] tokens = TokenGetter.getTokenTab(the_manager, a_mode);

    final IRule[] rules = createRulesArray(tokens);
    setRules(rules);
  }


  /**
   * The method creates an array of rules that are used in the colouring of
   * an edited bytecode document. The array has the size {@ref #NUMBER_OF_RULES}
   * and its elements are filled as the descriptions of the constants
   * <code>RULE_*</code> say:
   * <ul>
   *   <li> {@ref #RULE_EOL}
   *   <li> {@ref #RULE_INSTRUCTION}
   *   <li> {@ref #RULE_SEPARATOR}
   *   <li> {@ref #RULE_HASH}
   *   <li> {@ref #RULE_PERCENT}
   *   <li> {@ref #RULE_PARENTHESES}
   *   <li> {@ref #RULE_BRACES}
   *   <li> {@ref #RULE_NUMBER}
   *   <li> {@ref #RULE_WHITESPACE}
   *   <li> {@ref #RULE_STAR}
   *   <li> {@ref #RULE_COMMENT}
   * </ul>
   *
   * @param the_tokens the array of tokens that are returned when rules are
   *        applied
   *         TODO verify?
   * @return the array with the rules
   */
  private IRule[] createRulesArray(final IToken[] the_tokens) {
    //WordRule keyrule = new WordRule(new SpecialWordDetector(),
    //                                tokens[ColorValues.KEY]);
    final IRule[] rules = new IRule[NUMBER_OF_RULES];
    rules[RULE_EOL] = new EndOfLineRule("//", the_tokens[ColorValues.COMMENT]);
    rules[RULE_INSTRUCTION] = createInstructionRule(the_tokens);
    rules[RULE_SEPARATOR] = new SpecialNumberRule('\n', ':',
                     the_tokens[ColorValues.POSITION]);
    rules[RULE_HASH] = new SpecialNumberRule('#',
                     the_tokens[ColorValues.HASH]);
    rules[RULE_PERCENT] = new SpecialNumberRule('%',
                                                the_tokens[ColorValues.ATTR]);
    rules[RULE_PARENTHESES] = new SpecialNumberRule('(', ')',
                                           the_tokens[ColorValues.SQUARE]);
    //rules[6] = keyrule;
    rules[RULE_BRACES] = new SingleLineRule("{", "}",
                                            the_tokens[ColorValues.SQUARE]);
    rules[RULE_NUMBER] = new NumberRule(the_tokens[ColorValues.NUMBER]);
    rules[RULE_WHITESPACE] = new WhitespaceRule(
                                      new BytecodeWhitespaceDetector());
    rules[RULE_STAR] = new EndOfLineRule("*", the_tokens[ColorValues.ANNOT]);
    rules[RULE_COMMENT] = new EndOfLineRule("/*",
                                            the_tokens[ColorValues.ANNOT]);
    return rules;
  }


  /**
   * This method creates a rule used for colouring the instructions, BML
   * keywords, keywords in a "Line" line, and keywords in the "Code" line.
   * TODO more abstract description required
   *
   * @param the_tokens the array with tokens that are returned in different
   *        situations
   * @return the rule for colouring the instructions
   */
  private WordRule createInstructionRule(final IToken[] the_tokens) {
    final WordRule insrule = new WordRule(new BytecodeWordDetector(),
                                          the_tokens[ColorValues.DEFAULT]);
    tokensForInstructions(the_tokens, insrule);
    tokensForBMLKeywords(the_tokens, insrule);
    tokensForLinewords(the_tokens, insrule);
    tokensForCodeline(the_tokens, insrule);
    return insrule;
  }


  /**
   * This method associates in <code>the_insrule</code> the words which
   * occur in a line with the "Code" keyword with the token in
   * <code>the_tokens</code> under {@ref ColorValues#LINE}.
   * TODO - better description needed
   *
   * @param the_tokens the array with tokens, in particular with the
   *                   {@ref ColorValues#LINE} token
   * @param the_insrule the rule in which the association is created
   */
  private void tokensForCodeline(final IToken[] the_tokens,
                                 final WordRule the_insrule) {
    for (int i = 0; i < BytecodeStrings.CODE_KEYWORDS.length; i++) {
      the_insrule.addWord(BytecodeStrings.CODE_KEYWORDS[i],
              the_tokens[ColorValues.LINE]);
    }
  }


  /**
   * This method associates in <code>the_insrule</code> the words which
   * occur in a line with the "Line" keyword with the token in
   * <code>the_tokens</code> under {@ref ColorValues#LINE}.
   * TODO - better description needed
   *
   * @param the_tokens the array with tokens, in particular with the
   *                   {@ref ColorValues#LINE} token
   * @param the_insrule the rule in which the association is created
   */
  private void tokensForLinewords(final IToken[] the_tokens,
                                  final WordRule the_insrule) {
    for (int i = 0; i < BytecodeStrings.LINE_KEYWORDS.length; i++) {
      the_insrule.addWord(BytecodeStrings.LINE_KEYWORDS[i],
              the_tokens[ColorValues.LINE]);
    }
  }


  /**
   * This method associates in <code>the_insrule</code> the BML keywords
   * with the token in <code>the_tokens</code> under
   * {@ref ColorValues#ANNOTKEY}.
   * TODO - better description needed
   *
   * @param the_tokens the array with tokens, in particular with the
   *                   {@ref ColorValues#ANNOTKEY} token
   * @param the_insrule the rule in which the association is created

   */
  private void tokensForBMLKeywords(final IToken[] the_tokens,
                                    final WordRule the_insrule) {
    for (int i = 0; i < BytecodeStrings.BML_KEYWORDS.length; i++) {
      the_insrule.addWord(BytecodeStrings.BML_KEYWORDS[i],
              the_tokens[ColorValues.ANNOTKEY]);
    }
  }


  /**
   * This method associates in <code>the_insrule</code> the words of the
   * bytecode instructions with the token in <code>the_tokens</code> under
   * {@ref ColorValues#BTC_INSTR}.
   * TODO - better description needed
   *
   * @param the_tokens the array with tokens, in particular with the
   *                   {@ref ColorValues#BTC_INSTR} token
   * @param the_insrule the rule in which the association is created
  */
  private void tokensForInstructions(final IToken[] the_tokens,
                                     final WordRule the_insrule) {
    for (int i = 0; i < BytecodeStrings.INSTRUCTIONS.length; i++) {
      the_insrule.addWord(BytecodeStrings.INSTRUCTIONS[i],
              the_tokens[ColorValues.BTC_INSTR]);
    }
  }
}
