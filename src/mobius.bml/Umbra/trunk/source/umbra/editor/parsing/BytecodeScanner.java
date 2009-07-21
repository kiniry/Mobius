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
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.NumberRule;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

import umbra.lib.BytecodeStrings;



/**
 * This class is responsible for colouring these texts in a byte code
 * editor window which are outside BML annotations areas. This class uses
 * special 10 rules which describe the way the different areas are
 * coloured. Colours are chosen as a token array with a particular colouring
 * style given in the constructor.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeScanner extends RuleBasedScanner {

  /**
   * The number of the rule which is responsible for colour and text styling of
   * the end-of-line comments.
   */
  private static final int RULE_EOL = 0;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * the words (as defined in {@link BytecodeWordDetector}.
   */
  private static final int RULE_WORDS = 1;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * the byte code instruction numbers at the beginning of a method line.
   */
  private static final int RULE_INS_NUMBER = 2;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * the numbers preceded by the hash (#) sign.
   */
  private static final int RULE_HASH = 3;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * the numbers preceded by the percent (%) sign.
   */
  private static final int RULE_PERCENT = 4;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * the numbers enclosed in the parentheses ('(', ')').
   */
  private static final int RULE_PARENTHESES = 5;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * the line parts enclosed in the braces ('{', '}').
   */
  private static final int RULE_BRACES = 6;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * the numbers (without #, %, or surrounding parenteses).
   */
  private static final int RULE_NUMBER = 7;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * the whitespace areas.
   */
  private static final int RULE_WHITESPACE = 8;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * BML annotations areas ending with @*\/.
   */
  private static final int RULE_ANNOT = 9;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * BML annotations areas ending with *\/.
   */
  private static final int RULE_ANNOT_SIMPLE = 10;

  /**
   * The number of the rule which is responsible for colour and text styling of
   * comments.
   */
  private static final int RULE_COMMENT = 11;

  /**
   * The number of colouring rules used in this class.
   */
  private static final int NUMBER_OF_RULES = RULE_COMMENT + 1;


  /**
   * The constructor initialises the scanning rules for the current scanner.
   * It creates and the scanning rules taking into account the given colour
   * manager and colouring mode. It creates the rules to recognise all the
   * 10 rules:
   * <ul>
   *   <li> end-of-line comments,</li>
   *   <li> words,</li>
   *   <li> instruction number labels,</li>
   *   <li> numbers starting with '#',</li>
   *   <li> numbers starting with '%',</li>
   *   <li> numbers in parentheses '(', ')',</li>
   *   <li> line sections in braces '{', '}',</li>
   *   <li> bare numbers,</li>
   *   <li> whitespace,</li>
   *   <li> comments.</li>
   * </ul>
   *
   * @param the_manager the colour manager related to the current byte code
   *    editor, it must be the same as in the current
   *    {@link umbra.editor.BytecodeConfiguration} object
   * @param a_mode the number of the current colouring style, it must be the
   *    same as in the current {@link umbra.editor.BytecodeConfiguration} object
   */
  public BytecodeScanner(final ColorManager the_manager, final int a_mode) {

    final IToken[] tokens = TokenGetter.getTokenTab(the_manager, a_mode);

    final IRule[] rules = createRulesArray(tokens);
    setRules(rules);
  }


  /**
   * The method creates an array of rules that are used in the colouring of
   * an edited byte code document. The array has the size  #NUMBER_OF_RULES}
   * and its elements are filled as the descriptions of the constants
   * <code>RULE_*</code> say:
   * <ul>
   *   <li> {@link #RULE_EOL} for end-of-line comments,</li>
   *   <li> {@link #RULE_WORDS} for words,</li>
   *   <li> {@link #RULE_INS_NUMBER} for instruction number labels,</li>
   *   <li> {@link #RULE_HASH} for numbers starting with '#',</li>
   *   <li> {@link #RULE_PERCENT} for numbers starting with '%',</li>
   *   <li> {@link #RULE_PARENTHESES} for numbers in parentheses '(', ')',</li>
   *   <li> {@link #RULE_BRACES} for line sections in braces '{', '}',</li>
   *   <li> {@link #RULE_NUMBER} for bare numbers,</li>
   *   <li> {@link #RULE_WHITESPACE} for whitespace,</li>
   *   <li> {@link #RULE_COMMENT} for comments.</li>
   * </ul>
   *
   * @param the_tokens the array of tokens that are returned when rules are
   *        applied
   * @return the array with the rules
   */
  private IRule[] createRulesArray(final IToken[] the_tokens) {
    final IRule[] rules = new IRule[NUMBER_OF_RULES];
    rules[RULE_EOL] = new EndOfLineRule("//",
                                        the_tokens[ColorValues.SLOT_COMMENT]);
    rules[RULE_WORDS] = createInstructionRule(the_tokens);
    rules[RULE_INS_NUMBER] = new SpecialNumberRule('\n', ':',
      the_tokens[ColorValues.SLOT_LABELNUMBER]);
    rules[RULE_HASH] = new SpecialNumberRule('#',
      the_tokens[ColorValues.SLOT_HASH]);
    rules[RULE_PERCENT] = new SpecialNumberRule('%',
      the_tokens[ColorValues.SLOT_PERCENT]);
    rules[RULE_PARENTHESES] = new SpecialNumberRule('(', ')',
      the_tokens[ColorValues.SLOT_PARENTHESES]);
    rules[RULE_BRACES] = new SingleLineRule("{", "}",
      the_tokens[ColorValues.SLOT_PARENTHESES]);
    rules[RULE_NUMBER] = new NumberRule(the_tokens[ColorValues.SLOT_NUMBER]);
    rules[RULE_WHITESPACE] = new WhitespaceRule(
      new BytecodeWhitespaceDetector());

    rules[RULE_ANNOT] = new MultiLineRule(BytecodeStrings.ANNOT_START,
                                          BytecodeStrings.ANNOT_END,
                                          the_tokens[ColorValues.SLOT_TAG]);
    rules[RULE_ANNOT_SIMPLE] = new MultiLineRule(
                                          BytecodeStrings.ANNOT_START,
                                          BytecodeStrings.ANNOT_END_SIMPLE,
                                          the_tokens[ColorValues.SLOT_TAG]);
    rules[RULE_COMMENT] = new MultiLineRule("/*", "*/",
      the_tokens[ColorValues.SLOT_COMMENT]);
    return rules;
  }


  /**
   * This method creates a rule used for colouring various kinds of words
   * that occur in a byte code document. It assigns the
   * {@link ColorValues#SLOT_DEFAULT} colour as the default colour for words.
   * Except for that it assigns special colouring rules for the word categories:
   * the byte code instructions, keywords in a "Line"
   * section, and keywords in the "Code" section.
   *
   * @param the_tokens the array with tokens that describe the colour styling
   *   information, in particular the token with the default colour and
   *   the tokens with the colours of the special word categories
   * @return the rule for colouring the words
   */
  private WordRule createInstructionRule(final IToken[] the_tokens) {
    final WordRule insrule = new WordRule(new BytecodeWordDetector(),
                                          the_tokens[ColorValues.SLOT_DEFAULT]);
    tokensForInstructions(the_tokens, insrule);
    tokensForLinewords(the_tokens, insrule);
    tokensForCodeline(the_tokens, insrule);
    return insrule;
  }


  /**
   * This method associates in <code>the_insrule</code> the words which
   * occur in a line with the "Code" keyword with the token in
   * <code>the_tokens</code> under {@link ColorValues#SLOT_LINE}.
   *
   * @param the_tokens the array with tokens, in particular with the
   *   {@link ColorValues#SLOT_LINE} token
   * @param the_insrule the rule in which the association is created
   */
  private void tokensForCodeline(final IToken[] the_tokens,
                                 final WordRule the_insrule) {
    for (int i = 0; i < BytecodeStrings.CODE_KEYWORDS.length; i++) {
      the_insrule.addWord(BytecodeStrings.CODE_KEYWORDS[i],
              the_tokens[ColorValues.SLOT_LINE]);
    }
  }


  /**
   * This method associates in <code>the_insrule</code> the words which
   * occur in a line with the "Line" keyword with the token in
   * <code>the_tokens</code> under {@link ColorValues#SLOT_LINE}.
   *
   * @param the_tokens the array with tokens, in particular with the
   *   {@link ColorValues#SLOT_LINE} token
   * @param the_insrule the rule in which the association is created
   */
  private void tokensForLinewords(final IToken[] the_tokens,
                                  final WordRule the_insrule) {
    for (int i = 0; i < BytecodeStrings.LINE_KEYWORDS.length; i++) {
      the_insrule.addWord(BytecodeStrings.LINE_KEYWORDS[i],
              the_tokens[ColorValues.SLOT_LINE]);
    }
  }

  /**
   * This method associates in <code>the_insrule</code> the words of the
   * byte code instructions with the token in <code>the_tokens</code> under
   * {@link ColorValues#SLOT_BTCINSTR}.
   *
   * @param the_tokens the array with tokens, in particular with the
   *   {@link ColorValues#SLOT_BTCINSTR} token
   * @param the_insrule the rule in which the association is created
  */
  private void tokensForInstructions(final IToken[] the_tokens,
                                     final WordRule the_insrule) {
    for (int i = 0; i < BytecodeStrings.INSTRUCTIONS.length; i++) {
      the_insrule.addWord(BytecodeStrings.INSTRUCTIONS[i],
              the_tokens[ColorValues.SLOT_BTCINSTR]);
    }
  }
}
