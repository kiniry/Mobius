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
 * Colors are chosen as a token array with a particular style (param 'mod').
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeScanner extends RuleBasedScanner {

  /**
   * TODO
   */
  private static final int RULE_EOL = 0;
  
  /**
   * TODO
   */
  private static final int RULE_INSTRUCTION = 1;
  
  /**
   * TODO
   */
  private static final int RULE_SEPARATOR = 2;
  /**
   * TODO
   */
  private static final int RULE_HASH = 3;
  /**
   * TODO
   */
  private static final int RULE_PERCENT = 4;
  /**
   * TODO
   */
  private static final int RULE_PARENTHESES = 5;
  /**
   * TODO
   */
  private static final int RULE_BRACES = 6;
  /**
   * TODO
   */
  private static final int RULE_NUMBER = 7;
  /**
   * TODO
   */
  private static final int RULE_WHITESPACE = 8;
  /**
   * TODO
   */
  private static final int RULE_STAR = 9;
  /**
   * TODO
   */
  private static final int RULE_COMMENT = 10;

  /**
   * TODO
   */
  private static final int NUMBER_OF_RULES = 11;


  /**
   * This method TODO
   * sets the scanning rules
   *
   *
   * @param manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param mod the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   */
  public BytecodeScanner(final ColorManager manager, final int mod) {

    final IToken[] tokens = TokenGetter.getTokenTab(manager, mod);

    final WordRule insrule = new WordRule(new BytecodeWordDetector(),
                    tokens[IColorValues.DEFAULT]);
    for (int i = 0; i < IBytecodeStrings.instructions.length; i++) {
      insrule.addWord(IBytecodeStrings.instructions[i],
              tokens[IColorValues.BTC_INSTR]);
    }

    for (int i = 0; i < IBytecodeStrings.BMLKeywords.length; i++) {
      insrule.addWord(IBytecodeStrings.BMLKeywords[i],
              tokens[IColorValues.ANNOTKEY]);
    }

    for (int i = 0; i < IBytecodeStrings.linewords.length; i++) {
      insrule.addWord(IBytecodeStrings.linewords[i],
              tokens[IColorValues.LINE]);
    }

    for (int i = 0; i < IBytecodeStrings.code.length; i++) {
      insrule.addWord(IBytecodeStrings.code[i],
              tokens[IColorValues.LINE]);
    }

    //WordRule keyrule = new WordRule(new SpecialWordDetector(), tokens[IColorValues.KEY]);

    final IRule[] rules = new IRule[NUMBER_OF_RULES];
    rules[RULE_EOL] = new EndOfLineRule("//", tokens[IColorValues.COMMENT]);
    rules[RULE_INSTRUCTION] = insrule;
    rules[RULE_SEPARATOR] = new SpecialNumberRule('\n', ':',
                     tokens[IColorValues.POSITION]);
    rules[RULE_HASH] = new SpecialNumberRule('#',
                     tokens[IColorValues.HASH]);
    rules[RULE_PERCENT] = new SpecialNumberRule('%', tokens[IColorValues.ATTR]);
    rules[RULE_PARENTHESES] = new SpecialNumberRule('(', ')', tokens[IColorValues.SQUARE]);
    //rules[6] = keyrule;
    rules[RULE_BRACES] = new SingleLineRule("{", "}", tokens[IColorValues.SQUARE]);
    rules[RULE_NUMBER] = new NumberRule(tokens[IColorValues.NUMBER]);
    rules[RULE_WHITESPACE] = new WhitespaceRule(new BytecodeWhitespaceDetector());
    rules[RULE_STAR] = new EndOfLineRule("*", tokens[IColorValues.ANNOT]);
    rules[RULE_COMMENT] = new EndOfLineRule("/*", tokens[IColorValues.ANNOT]);

    setRules(rules);
  }
}
