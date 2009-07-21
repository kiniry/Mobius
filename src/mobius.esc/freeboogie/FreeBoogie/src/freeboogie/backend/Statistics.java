package freeboogie.backend;

import java.util.HashMap;
import java.util.HashSet;

/**
 * Experimental class used to collect statistics about terms.
 */
public final class Statistics {
  private Statistics() { /* forbid instantiation */ }

  public static int printSize(SmtTerm t) {
    Integer result = sizes.get(t);
    if (result != null) return result;
    result = 1;
    for (SmtTerm c : t.children) result += printSize(c);
    sizes.put(t, result);
    return result;
  }

  private static HashMap<SmtTerm, Integer> sizes =
    new HashMap<SmtTerm, Integer>(100003);

  public static int nodesCount(SmtTerm t) {
    seen.clear();
    return recNodesCount(t);
  }

  private static HashSet<SmtTerm> seen = new HashSet<SmtTerm>(100003);

  private static int recNodesCount(SmtTerm t) {
    if (seen.contains(t)) return 0;
    seen.add(t);
    int result = 1;
    for (SmtTerm c : t.children) result += recNodesCount(c);
    return result;
  }
}
