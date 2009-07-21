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
 * This method defines coloring rules in tags.
 * It has been generated automatically except obtaing
 * color values from the array in {@ref ColorValues}.
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLTagScanner extends RuleBasedScanner {

  /**
   * TODO.
   * @param the_manager the manager which manages the color allocation
   * @param a_mode the current colouring mode
   */
  public BoogiePLTagScanner(final ColorManager the_manager,
                            final int a_mode) { /*
    IToken[] tokens = TokenGetter.getTokenTab(manager, mod);

    WordRule linerule = new WordRule(new SpecialWordDetector());
      linerule.addWord("<init>", tokens[ColorValues.KEY]);

    IRule[] rules = new IRule[4];

    // Add rule for double quotes
    rules[0] = new SingleLineRule("\"", "\"", tokens[ColorValues.STRING],
                                  '\\');
    // Add a rule for single quotes
    rules[1] = new SingleLineRule("'", "'", tokens[ColorValues.STRING], '\\');
    // Add generic whitespace rule.
    rules[2] = linerule;
    rules[3] = new WhitespaceRule(new BoogiePLWhitespaceDetector());

    setRules(rules);
    */
  }
}
