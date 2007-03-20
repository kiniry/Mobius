/** Public domain. */

package freeboogie.ast.gen;

/**
 * TODO describe
 * 
 * I'll use the convention that an empty token is described by two
 * pointers just before it.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class TokenLocation extends Location<AgToken> {
  private CharLocation begin;
  private CharLocation end;
  
  /**
   * Initializes a {@code TokenLocation}.
   */
  public TokenLocation() {
    begin = end = new CharLocation();
  }
  
  /**
   * Copy constructor.
   * @param other the object to copy
   */
  public TokenLocation(TokenLocation other) {
    begin = other.begin;
    end = other.end;
  }

  @Override
  public Location<AgToken> advance(AgToken element) {
    TokenLocation r = new TokenLocation(this);
    r.begin = r.end;
    if (element.rep.length() > 0)
      r.begin = (CharLocation)r.begin.advance(element.rep.charAt(0));
    for (int i = 0; i < element.rep.length(); ++i)
      r.end = (CharLocation)r.end.advance(element.rep.charAt(i));
    return r;
  }
  
  @Override
  public String toString() {
    return "" + begin + "--" + end;
  }

  /**
   * TODO testing
   * @param args
   */
  public static void main(String[] args) {
    // TODO Auto-generated method stub
  }
}
