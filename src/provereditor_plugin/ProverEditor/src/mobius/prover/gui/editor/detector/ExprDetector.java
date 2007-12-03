package mobius.prover.gui.editor.detector;

import org.eclipse.jface.text.rules.IWordDetector;
/**
 * A basic implementation of a detector to detect expressions for a prover.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ExprDetector implements IWordDetector {


  /** {@inheritDoc} */
  @Override
  public boolean isWordStart(final char c) {
    return c == '-' || c == '<' || c == '>' ||
      c == ':' || c == '.' || c == ',';
  }

 
  /** {@inheritDoc} */
  @Override
  public boolean isWordPart(final char c) {
    return isWordStart(c);
  }

}
