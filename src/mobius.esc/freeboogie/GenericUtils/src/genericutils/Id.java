package genericutils;

import java.util.HashMap;
import java.util.Map;

/**
 * Provides (almost) unique identifiers.
 *
 * @author rgrig
 */
public final class Id {
  private Id() { /* forbid instantiation */ }

  private static Map<String, Integer> counter =
    new HashMap<String, Integer>();
  private static StringBuilder sb = new StringBuilder();
  private static char[] buf = new char[10];
  private static final int SZ = 'z' - 'a' + 1;

  /** 
   * Returns a (hopefully) unique identifier that contains
   * the string {@code categ}.
   */
  public static String get(String categ) {
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
