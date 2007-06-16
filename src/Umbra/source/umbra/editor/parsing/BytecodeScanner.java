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

    final IRule[] rules = new IRule[11];
    rules[0] = new EndOfLineRule("//", tokens[IColorValues.COMMENT]);
    rules[1] = insrule;
    rules[2] = new SpecialNumberRule('\n', ':',
                     tokens[IColorValues.POSITION]);
    rules[3] = new SpecialNumberRule('#',
                     tokens[IColorValues.HASH]);
    rules[4] = new SpecialNumberRule('%', tokens[IColorValues.ATTR]);
    rules[5] = new SpecialNumberRule('(', ')', tokens[IColorValues.SQUARE]);
    //rules[6] = keyrule;
    rules[6] = new SingleLineRule("{", "}", tokens[IColorValues.SQUARE]);
    rules[7] = new NumberRule(tokens[IColorValues.NUMBER]);
    rules[8] = new WhitespaceRule(new BytecodeWhitespaceDetector());
    rules[9] = new EndOfLineRule("*", tokens[IColorValues.ANNOT]);
    rules[10] = new EndOfLineRule("/*", tokens[IColorValues.ANNOT]);

    setRules(rules);
  }
}
