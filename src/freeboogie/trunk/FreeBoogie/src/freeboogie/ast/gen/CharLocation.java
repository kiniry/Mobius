/** Public domain. */

package freeboogie.ast.gen;

/**
 * A simple line column structure.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class CharLocation extends Location<Character> {
  private int line, col;
  private boolean eof;
  
  /** Initializiation */
  public CharLocation() {
    line = col = 0;
    eof = false;
  }
  
  /**
   * Copy constructor.
   * @param other the other object
   */
  public CharLocation(CharLocation other) {
    line = other.line;
    col = other.col;
    eof = other.eof;
  }
  
  @Override
  public void advance(Character element) {
    if (element == null) eof = true;
    if (eof) return;
    if (element == '\n') {
      ++line; col = 0;
    } else ++col;
  }
  
  @Override
  public String toString() {
    if (eof) return "EOF";
    return "(" + (line + 1) + ", " + (col + 1) + ")";
  }

}
