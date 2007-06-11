package umbra.editor.boogiepl;

import org.eclipse.jface.text.rules.RuleBasedScanner;

import umbra.editor.ColorManager;


/**
 * This class is responsible for coloring all text in BoogiePL
 * editor window according to some special 9 rules.
 * Colors are chosen as a token array with a particular style (param 'mod').
 *
 * @author Samuel Willimann
 */
public class BoogiePLScanner extends RuleBasedScanner {

  /**
   * TODO
   */
  public BoogiePLScanner(ColorManager manager, int mod) {
    /*
    IToken[] tokens = TokenGetter.getTokenTab(manager, mod);

    WordRule insrule = new WordRule(new BoogiePLWordDetector(), tokens[IColorValues.DEFAULT]);
    for (int i = 0; i < IBoogiePLStrings.instructions.length; i++) {
      insrule.addWord(IBoogiePLStrings.instructions[i], tokens[IColorValues.BTC_INSTR]);
    }

    WordRule keyrule = new WordRule(new SpecialWordDetector(), tokens[IColorValues.KEY]);

    IRule[] rules = new IRule[9];
    rules[0] = new EndOfLineRule("//", tokens[IColorValues.COMMENT]);
    rules[1] = insrule;
    rules[2] = new SpecialNumberRule('\n', ':', tokens[IColorValues.POSITION]);
    rules[3] = new SpecialNumberRule('#', tokens[IColorValues.HASH]);
    rules[4] = new SpecialNumberRule('%', tokens[IColorValues.ATTR]);
    rules[5] = new SpecialNumberRule('(', ')', tokens[IColorValues.SQUARE]);
    //rules[6] = keyrule;
    rules[6] = new SingleLineRule("{", "}", tokens[IColorValues.SQUARE]);
    rules[7] = new NumberRule(tokens[IColorValues.NUMBER]);
    rules[8] = new WhitespaceRule(new BoogiePLWhitespaceDetector());

    setRules(rules);
    */
  }
}
