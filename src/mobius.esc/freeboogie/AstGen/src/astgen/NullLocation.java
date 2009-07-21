package astgen;

/**
 * Does not track location.
 * 
 * @author rgrig 
 * @param <T> type
 */
public class NullLocation<T> extends Location<T> {
  
  @Override
  public Location<T> advance(@SuppressWarnings("unused") T element) {
    return this;
  }
  
  @Override
  public String toString() {
    return "(location not tracked)";
  }
}
