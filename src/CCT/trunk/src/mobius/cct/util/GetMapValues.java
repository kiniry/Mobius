package mobius.cct.util;

import java.util.Iterator;
import java.util.Map;

/**
 * A function which returns iterator over values from a map.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <K> Type of map keys.
 * @param <V> Type of map values.
 */
public class GetMapValues<K, V> implements 
  Function<Map<K, V>, Iterator<V>> {
  
  /**
   * Call function.
   * @param args Source collection.
   * @return Iterator.
   */
  public Iterator<V> call(final Map<K, V> args) {
    return args.values().iterator();
  }

}
