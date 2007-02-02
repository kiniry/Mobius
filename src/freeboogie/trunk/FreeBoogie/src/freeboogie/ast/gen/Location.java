/** Public domain. */

package freeboogie.ast.gen;

/**
 * Interface for stream location tracking.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 * @param <T> the type of the stream element
 */
public interface Location<T> {
  
  /**
   * Advance the location by one element.
   * @param element the last element eaten (read) from the stream
   */
  public void advance(T element);
  
  /**
   * Returns a human-readable description of the location of the last
   * element received as a parameter by advance.
   * 
   * TODO: how to make it mandatory to implement this?
   * 
   * @return a human-readable description of the location
   */
  public String toString();

}
