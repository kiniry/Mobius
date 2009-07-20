package mobius.prover.gui.editor;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;

/**
 * A rule to detect words of a fixed size.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class FixedSizeWordRule extends WordRule {
  /** the size of the word. */
  private int fSize;
  /** Buffer used for pattern detection. */
  private StringBuffer fBuffer = new StringBuffer();
  
  /**
   * Create a new word rule.
   * @param detector a word detector
   * @param size the size of a word
   */
  public FixedSizeWordRule(final IWordDetector detector, 
                           final int size) {
    super(detector);
    fSize = size;
  }
  
  
  /** {@inheritDoc} */
  @Override
  public IToken evaluate(final ICharacterScanner scanner) {
    int c = scanner.read();
    if (fDetector.isWordStart((char) c)) {
      if (fColumn == UNDEFINED || (fColumn == scanner.getColumn() - 1)) {

        fBuffer.setLength(0);
        int i = 0;
        do {
          fBuffer.append((char) c);
          c = scanner.read();
          i++;
        } while (c != ICharacterScanner.EOF && fDetector.isWordPart((char) c) && (i < fSize));
        scanner.unread();

        final IToken token = (IToken) fWords.get(fBuffer.toString());
        if (token != null) {
          return token;
        }

        if (fDefaultToken.isUndefined()) {
          unreadBuffer(scanner);
        }

        return fDefaultToken;
      }
    }

    scanner.unread();
    return Token.UNDEFINED;
  }

  /** {@inheritDoc} */
  @Override
  protected void unreadBuffer(final ICharacterScanner scanner) {
    for (int i = fBuffer.length() - 1; i >= 0; i--) {
      scanner.unread();
    }
  }
}
