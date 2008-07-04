package freeboogie.util;

import java.util.HashMap;
import java.util.Map;

/**
 * Provides (almost) unique identifiers.
 *
 * @author rgrig
 */
public class Id {
  static private Map<String, Integer> counter =
    new HashMap<String, Integer>();
  static private StringBuilder sb = new StringBuilder();
  static private char[] buf = new char[10];
  static private final int SZ = 'z' - 'a' + 1;

  /** 
   * Returns a (hopefully) unique identifier that contains
   * the string {@code categ}.
   */
  static public String get(String categ) {
    int i, j, k;
    int y;
    Integer x = counter.get(categ);
    y = x == null? 0 : x + 1;
    counter.put(categ, y);
    sb.setLength(0);
    sb.append("$$");
    sb.append(categ);
    sb.append("~");
    for (k = 0, j = SZ; y >= j; ++k, j *= SZ) y -= j;
    for (i = k; i >= 0; --i, y /= SZ)
      buf[i] = (char)(y % SZ + 'a');
    for (i = 0; i <= k; ++i) sb.append(buf[i]);
    return sb.toString();
  }
}
