package umbra.editor.boogiepl;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

/**
 * New definition of whitespace
 *
 * @author Samuel Willimann
 */
public class BoogiePLWhitespaceDetector implements IWhitespaceDetector {

  /**
   * TODO
   */
  public boolean isWhitespace(char c) {
    return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
  }
}
