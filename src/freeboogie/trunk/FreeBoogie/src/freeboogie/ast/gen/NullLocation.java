/** Public domain. */

package freeboogie.ast.gen;

/**
 * Does not track location.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 * @param <T> type
 */
public class NullLocation<T> extends Location<T> {

  @Override
  public void advance(@SuppressWarnings("unused") T element) {
    // Do nothing
  }
  
  @Override
  public String toString() {
    return "(location not tracked)";
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
