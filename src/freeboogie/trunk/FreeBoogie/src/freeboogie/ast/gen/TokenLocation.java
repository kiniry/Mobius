/** Public domain. */

package freeboogie.ast.gen;

import freeboogie.util.Err;

/**
 * @author rgrig 
 * @author reviewed by TODO
 *
 */
public class TokenLocation implements Location<AgToken> {
  private CharLocation begin;
  private CharLocation end;
  
  /**
   * Initializes a {@code TokenLocation}.
   */
  public TokenLocation() {
    begin = null;
    end = new CharLocation();
  }

  /* @see freeboogie.ast.gen.Location#advance(java.lang.Object) */
  public void advance(AgToken element) {
    begin = new CharLocation(end);
    for (int i = 0; i < element.rep.length(); ++i)
      end.advance(element.rep.charAt(i));
  }
  
  @Override
  public String toString() {
    return "" + begin + "--" + end;
  }

  /**
   * @param args
   */
  public static void main(String[] args) {
  // TODO Auto-generated method stub

  }

}
