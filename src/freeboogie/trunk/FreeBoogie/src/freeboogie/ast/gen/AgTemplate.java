/** Public domain. */

package freeboogie.ast.gen;

import java.io.IOException;

/**
 * TODO: description
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class AgTemplate extends PeekStream<String> {
  
  /**
   * @param fileName
   */
  public AgTemplate(String fileName) throws IOException {
    super(new NullLocation<String>()); // TODO track location?
    // TODO
  }

  /**
   * @param grammar
   */
  public void process(Grammar grammar) throws IOException {
    // TODO Auto-generated method stub
    
  }

  /* @see freeboogie.ast.gen.PeekStream#read() */
  @Override
  protected String read() throws IOException {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * TODO testing
   * @param args
   */
  public static void main(String[] args) {
    // TODO Auto-generated method stub
  }
}
