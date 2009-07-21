package mobius.cct.util;

import java.util.Collection;
import java.util.Iterator;

/**
 * A function which returns iterator of a collection.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <T> Type of collection elements.
 */
public class GetIterator<T> implements 
  Function<Collection<T>, Iterator<T>> {
  
  /**
   * Call function.
   * @param args Source collection.
   * @return Iterator.
   */
  public Iterator<T> call(final Collection<T> args) {
    return args.iterator();
  }

}
