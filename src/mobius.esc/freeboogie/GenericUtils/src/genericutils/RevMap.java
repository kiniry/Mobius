package genericutils;

import java.util.HashMap;
import java.util.LinkedHashMap;

/** 
 * Stores a set of pairs, with fast lookup given any component. 
 * The implementation uses {@code HashMap} so the usual restrictions
 * apply ({@code equals}, {@code hashCode}, and so on).
 * @param <U> the type of the first element of pairs
 * @param <V> the type of the second element of pairs
 */
public class RevMap<U,V> {
  private HashMap<U,V> utov;
  private HashMap<V,U> vtou;

  private static boolean isPrime(int x) {
    if (x % 2 == 0) return false;
    for (int i = 3; i * i < x; i += 2)
      if (x % i == 0) return false;
    return true;
  }

  /** Initialize the mapping with {@code size}. */
  public RevMap(int size) {
    assert isPrime(size);
    utov = new LinkedHashMap<U,V>(size);
    vtou = new LinkedHashMap<V,U>(size);
  }

  /** Store the pair (u, v). */
  public void store(U u, V v) {
    utov.put(u, v);
    vtou.put(v, u);
  }

  public V searchByU(U u) { return utov.get(u); }
  public U searchByV(V v) { return vtou.get(v); }

  public void removeByU(U u) {
    V v = utov.remove(u);
    if (v != null) vtou.remove(v);
  }

  public void removeByV(V v) {
    U u = vtou.remove(v);
    if (u != null) utov.remove(u);
  }
}
