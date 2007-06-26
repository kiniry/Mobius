package umbra.editor.parsing;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

import umbra.editor.ColorManager;
import umbra.editor.IColorValues;
import umbra.editor.parsing.BytecodeWhitespaceDetector;
import umbra.editor.parsing.SpecialWordDetector;

/**
 * This method defines coloring rules in tags.
 * It has been generated automatically except obtaing
 * color values from the array in IColorValues.
 */
public class BytecodeTagScanner extends RuleBasedScanner {

  /**
   * TODO.
   */
  private static final int DOUBLE_QUOTE_RULE = 0;

  /**
   * TODO.
   */
  private static final int SINGLE_QUOTE_RULE = 1;

  /**
   * TODO.
   */
  private static final int LINE_RULE = 2;

  /**
   * TODO.
   */
  private static final int WHITESPACE_RULE = 3;

  /**
   * TODO.
   */
  private static final int RULES_NUMBER = 4;

  /**
   * TODO
   *
   * @param manager the color manager related to the current bytecode
   *    editor, it must be the same as in the current
   *    {@ref BytecodeConfiguration} object
   * @param mod the number of the current coloring style, it must be the
   *    same as in the current {@ref BytecodeConfiguration} object
   */
  public BytecodeTagScanner(final ColorManager manager, final int mod) {

    final IToken[] tokens = TokenGetter.getTokenTab(manager, mod);

    final WordRule linerule = new WordRule(new SpecialWordDetector());
    linerule.addWord("<init>", tokens[IColorValues.KEY]);

    final IRule[] rules = new IRule[RULES_NUMBER];

    // Add rule for double quotes
    rules[DOUBLE_QUOTE_RULE] = new SingleLineRule("\"", "\"",
                                                  tokens[IColorValues.STRING],
                                                  '\\');
    // Add a rule for single quotes
    rules[SINGLE_QUOTE_RULE] = new SingleLineRule("'", "'", tokens[IColorValues.STRING], '\\');
    // Add generic whitespace rule.
    rules[LINE_RULE] = linerule;
    rules[WHITESPACE_RULE] = new WhitespaceRule(new BytecodeWhitespaceDetector());

    setRules(rules);
  }
}
