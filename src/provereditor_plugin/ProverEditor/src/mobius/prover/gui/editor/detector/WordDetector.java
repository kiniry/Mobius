package mobius.prover.gui.editor.detector;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * A basic implementation to detect words for a prover.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class WordDetector implements IWordDetector {

  /** {@inheritDoc} */
  @Override
  public boolean isWordStart(final char c) {
    return Character.isLetter(c);
  }

  /** {@inheritDoc} */
  @Override
  public boolean isWordPart(final char c) {
    return Character.isLetterOrDigit(c) || c == '_';
  }

}
