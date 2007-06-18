/*
 * Created on 2005-04-25
 *
 */
package umbra.editor.boogiepl;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * TODO
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLWordDetector implements IWordDetector {

  /**
   * TODO
   */
  public final boolean isWordStart(final char c) {
    return Character.isLetter(c);
  }

  /**
   * TODO
   */
  public final boolean isWordPart(final char c) {
    return (Character.isLetterOrDigit(c) || c == '_');
  }
}
