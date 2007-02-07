/** Public domain. */

package freeboogie.ast.gen;

import java.io.IOException;
import java.io.InputStream;

/**
 * TODO Description.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class CharStream extends PeekStream<Character> {
  
  private InputStream stream;
  
  /**
   * Sets the input stream.
   * @param stream the input stream
   */
  public CharStream(InputStream stream) {
    super(new CharLocation());
    this.stream = stream;
  }

  /* @see freeboogie.ast.gen.PeekStream#read() */
  @Override
  public Character read() throws IOException {
    Character r = null;
    int c = stream.read();
    if (c != -1) r = Character.valueOf((char) c);
    return r;
  }

  /**
   * For testing. (TODO)
   * 
   * @param args
   */
  public static void main(String[] args) {
  // TODO Auto-generated method stub

  }

}
