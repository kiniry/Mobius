package mobius.prover.gui.editor;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;

/**
 * A minimal implementation of a RuleBasedScanner.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class BasicRuleScanner extends RuleBasedScanner implements IColorConstants {

  /**
   * Create a new scanner.
   */
  public BasicRuleScanner() {
    this(null);
  }
  
  /**
   * Create a new scanner using the specified rules.
   * @param rules the rules to scan with.
   */
  public BasicRuleScanner(final IRule[] rules) {
    super();
    if (rules == null) {
      setRules(new IRule[0]);
    }
    else {
      setRules(rules);
    }
  }
  
  /**
   * Returns the default token.
   * @return the default token
   */
  public IToken getDefaultReturnToken() {
    return fDefaultReturnToken;
  }
}
