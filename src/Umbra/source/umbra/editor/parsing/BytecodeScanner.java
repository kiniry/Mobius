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
import umbra.editor.IColorValues;


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
    //                                tokens[IColorValues.KEY]);
    final IRule[] rules = new IRule[NUMBER_OF_RULES];
    rules[RULE_EOL] = new EndOfLineRule("//", the_tokens[IColorValues.COMMENT]);
    rules[RULE_INSTRUCTION] = createInstructionRule(the_tokens);
    rules[RULE_SEPARATOR] = new SpecialNumberRule('\n', ':',
                     the_tokens[IColorValues.POSITION]);
    rules[RULE_HASH] = new SpecialNumberRule('#',
                     the_tokens[IColorValues.HASH]);
    rules[RULE_PERCENT] = new SpecialNumberRule('%',
                                                the_tokens[IColorValues.ATTR]);
    rules[RULE_PARENTHESES] = new SpecialNumberRule('(', ')',
                                           the_tokens[IColorValues.SQUARE]);
    //rules[6] = keyrule;
    rules[RULE_BRACES] = new SingleLineRule("{", "}",
                                            the_tokens[IColorValues.SQUARE]);
    rules[RULE_NUMBER] = new NumberRule(the_tokens[IColorValues.NUMBER]);
    rules[RULE_WHITESPACE] = new WhitespaceRule(
                                      new BytecodeWhitespaceDetector());
    rules[RULE_STAR] = new EndOfLineRule("*", the_tokens[IColorValues.ANNOT]);
    rules[RULE_COMMENT] = new EndOfLineRule("/*",
                                            the_tokens[IColorValues.ANNOT]);
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
                                          the_tokens[IColorValues.DEFAULT]);
    tokensForInstructions(the_tokens, insrule);
    tokensForBMLKeywords(the_tokens, insrule);
    tokensForLinewords(the_tokens, insrule);
    tokensForCodeline(the_tokens, insrule);
    return insrule;
  }


  /**
   * This method associates in <code>the_insrule</code> the words which
   * occur in a line with the "Code" keyword with the token in
   * <code>the_tokens</code> under {@ref IColorValues#LINE}.
   * TODO - better description needed
   *
   * @param the_tokens the array with tokens, in particular with the
   *                   {@ref IColorValues#LINE} token
   * @param the_insrule the rule in which the association is created
   */
  private void tokensForCodeline(final IToken[] the_tokens,
                                 final WordRule the_insrule) {
    for (int i = 0; i < AbstractBytecodeStrings.CODE_KEYWORDS.length; i++) {
      the_insrule.addWord(AbstractBytecodeStrings.CODE_KEYWORDS[i],
              the_tokens[IColorValues.LINE]);
    }
  }


  /**
   * This method associates in <code>the_insrule</code> the words which
   * occur in a line with the "Line" keyword with the token in
   * <code>the_tokens</code> under {@ref IColorValues#LINE}.
   * TODO - better description needed
   *
   * @param the_tokens the array with tokens, in particular with the
   *                   {@ref IColorValues#LINE} token
   * @param the_insrule the rule in which the association is created
   */
  private void tokensForLinewords(final IToken[] the_tokens,
                                  final WordRule the_insrule) {
    for (int i = 0; i < AbstractBytecodeStrings.LINE_KEYWORDS.length; i++) {
      the_insrule.addWord(AbstractBytecodeStrings.LINE_KEYWORDS[i],
              the_tokens[IColorValues.LINE]);
    }
  }


  /**
   * This method associates in <code>the_insrule</code> the BML keywords
   * with the token in <code>the_tokens</code> under
   * {@ref IColorValues#ANNOTKEY}.
   * TODO - better description needed
   *
   * @param the_tokens the array with tokens, in particular with the
   *                   {@ref IColorValues#ANNOTKEY} token
   * @param the_insrule the rule in which the association is created

   */
  private void tokensForBMLKeywords(final IToken[] the_tokens,
                                    final WordRule the_insrule) {
    for (int i = 0; i < AbstractBytecodeStrings.BML_KEYWORDS.length; i++) {
      the_insrule.addWord(AbstractBytecodeStrings.BML_KEYWORDS[i],
              the_tokens[IColorValues.ANNOTKEY]);
    }
  }


  /**
   * This method associates in <code>the_insrule</code> the words of the
   * bytecode instructions with the token in <code>the_tokens</code> under
   * {@ref IColorValues#BTC_INSTR}.
   * TODO - better description needed
   *
   * @param the_tokens the array with tokens, in particular with the
   *                   {@ref IColorValues#BTC_INSTR} token
   * @param the_insrule the rule in which the association is created
  */
  private void tokensForInstructions(final IToken[] the_tokens,
                                     final WordRule the_insrule) {
    for (int i = 0; i < AbstractBytecodeStrings.INSTRUCTIONS.length; i++) {
      the_insrule.addWord(AbstractBytecodeStrings.INSTRUCTIONS[i],
              the_tokens[IColorValues.BTC_INSTR]);
    }
  }
}
