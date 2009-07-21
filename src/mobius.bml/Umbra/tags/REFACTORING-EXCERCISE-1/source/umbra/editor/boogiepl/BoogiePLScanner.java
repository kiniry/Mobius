/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
package umbra.editor.boogiepl;

import org.eclipse.jface.text.rules.RuleBasedScanner;

import umbra.editor.ColorManager;


/**
 * This class is responsible for coloring all text in BoogiePL
 * editor window according to some special 9 rules.
 * Colors are chosen as a token array with a particular style (param 'mod').
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLScanner extends RuleBasedScanner {

  /**
   * TODO.
   * @param the_manager the manager which manages the color allocation
   * @param a_mode the current colouring mode
   */
  public BoogiePLScanner(final ColorManager the_manager, final int a_mode) {
    /*
    IToken[] tokens = TokenGetter.getTokenTab(manager, mod);

    WordRule insrule = new WordRule(new BoogiePLWordDetector(),
                                    tokens[ColorValues.DEFAULT]);
    for (int i = 0; i < BoogiePLStrings.INSTRUCTIONS.length; i++) {
      insrule.addWord(BoogiePLStrings.INSTRUCTIONS[i],
                      tokens[ColorValues.BTC_INSTR]);
    }

    WordRule keyrule = new WordRule(new SpecialWordDetector(),
                                    tokens[ColorValues.KEY]);

    IRule[] rules = new IRule[9];
    rules[0] = new EndOfLineRule("//", tokens[ColorValues.COMMENT]);
    rules[1] = insrule;
    rules[2] = new SpecialNumberRule('\n', ':', tokens[ColorValues.POSITION]);
    rules[3] = new SpecialNumberRule('#', tokens[ColorValues.HASH]);
    rules[4] = new SpecialNumberRule('%', tokens[ColorValues.ATTR]);
    rules[5] = new SpecialNumberRule('(', ')', tokens[ColorValues.SQUARE]);
    //rules[6] = keyrule;
    rules[6] = new SingleLineRule("{", "}", tokens[ColorValues.SQUARE]);
    rules[7] = new NumberRule(tokens[ColorValues.NUMBER]);
    rules[8] = new WhitespaceRule(new BoogiePLWhitespaceDetector());

    setRules(rules);
    */
  }
}
