/** Public domain. */

package freeboogie.ast.gen;

/**
 * @author rgrig 
 * @author reviewed by TODO
 *
 */
public class TokenLocation extends Location<AgToken> {
  private CharLocation begin;
  private CharLocation end;
  
  /**
   * Initializes a {@code TokenLocation}.
   */
  public TokenLocation() {
    begin = null;
    end = new CharLocation();
  }

  @Override
  public void advance(AgToken element) {
    begin = new CharLocation(end);
    for (int i = 0; i < element.rep.length(); ++i)
      end.advance(element.rep.charAt(i));
  }
  
  @Override
  public String toString() {
    assert begin != null; // should not be called without any call to advance
    return "" + begin + "--" + end;
  }

  /**
   * @param args
   */
  public static void main(String[] args) {
  // TODO Auto-generated method stub

  }

}
