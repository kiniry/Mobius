package mobius.prover.simplify;

import org.eclipse.jface.text.rules.IWordDetector;
/**
 * A basic implementation of a detector to detect expressions for a prover.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ParenDetector implements IWordDetector {

  private int par; 

  /** {@inheritDoc} */
  public boolean isWordStart(final char c) {
    if (c == '(') {
      if (par == 0) { 
        par = 1;
      }
      return true;
    }
    return false;
  }

 
  /** {@inheritDoc} */
  public boolean isWordPart(final char c) {
    boolean res = true;
    if (par == 0 && !Character.isWhitespace(c)) {
      res = false;
    }
    if (c == '(') {
      par++;
    }
    else if (c == ')') {
      par--;
    }
    return res;
  }

}
