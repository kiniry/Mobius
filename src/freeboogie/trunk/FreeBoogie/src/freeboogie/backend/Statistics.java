package freeboogie.backend;

import java.util.HashMap;
import java.util.HashSet;

/**
 * Experimental class used to collect statistics about terms.
 */
public class Statistics {
  static public int printSize(SmtTerm t) {
    Integer result = sizes.get(t);
    if (result != null) return result;
    result = 1;
    for (SmtTerm c : t.children) result += printSize(c);
    sizes.put(t, result);
    return result;
  }

  static private HashMap<SmtTerm, Integer> sizes =
    new HashMap<SmtTerm, Integer>(100003);

  static public int nodesCount(SmtTerm t) {
    seen.clear();
    return recNodesCount(t);
  }

  static private HashSet<SmtTerm> seen = new HashSet<SmtTerm>(100003);

  static private int recNodesCount(SmtTerm t) {
    if (seen.contains(t)) return 0;
    seen.add(t);
    int result = 1;
    for (SmtTerm c : t.children) result += recNodesCount(c);
    return result;
  }
}
