package freeboogie.util;

import java.util.HashMap;
import java.util.Map;

public class Id {
  static private Map<String, Integer> counter =
    new HashMap<String, Integer>();

  static public String get(String categ) {
    Integer x = counter.get(categ);
    if (x == null) x = -1;
    counter.put(categ, ++x);
    return "tmp_" + categ + "_" + x;
  }
}
