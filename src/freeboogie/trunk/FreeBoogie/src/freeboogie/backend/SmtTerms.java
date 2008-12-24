package freeboogie.backend;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import freeboogie.util.Id;

/**
 * Utilities for handling {@code SmtTerm}s.
 */
public class SmtTerms {
  // === Functions for eliminating sharing ===
  
  /** Passed around by functions that eliminate sharing. */
  private static class EliminateSharingContext {
    public HashMap<SmtTerm, Integer> parentCount =
      new HashMap<SmtTerm, Integer>(31);
    public HashMap<SmtTerm, Integer> sizes =
      new HashMap<SmtTerm, Integer>(31);
    public HashMap<String, SmtTerm> varDefs =
      new HashMap<String, SmtTerm>(31);
    public HashMap<SmtTerm, SmtTerm> unshared =
      new HashMap<SmtTerm, SmtTerm>(31);
    public HashSet<SmtTerm> seen = new HashSet<SmtTerm>(31);
    public TermBuilder<SmtTerm> term;
  }

  public static SmtTerm eliminateSharing(SmtTerm t, TermBuilder<SmtTerm> term) {
    EliminateSharingContext context = new EliminateSharingContext();
    context.term = term;
    countParents(t, context);
    t = unshare(t, context);
    ArrayList<SmtTerm> defs =
      new ArrayList<SmtTerm>(context.varDefs.size());
    for (Map.Entry<String, SmtTerm> vd : context.varDefs.entrySet()) {
      defs.add(term.mk("iff",
        term.mk("var_formula", vd.getKey()),
        vd.getValue()));
    }
    return term.mk("implies", term.mk("and", defs), t);
  }

  private static void countParents(SmtTerm t, EliminateSharingContext context) {
    if (context.seen.contains(t)) return;
    context.seen.add(t);
    for (SmtTerm c : t.children) {
      Integer cnt = context.parentCount.get(c);
      if (cnt == null) cnt = 0;
      context.parentCount.put(c, cnt + 1);
      countParents(c, context);
    }
  }

  private static int getPrintSize(SmtTerm t, EliminateSharingContext context) {
    Integer result = context.sizes.get(t);
    if (result != null) return result;
    result = 1;
    for (SmtTerm c : t.children) result += getPrintSize(c, context);
    context.sizes.put(t, result);
    return result;
  }

  private static SmtTerm unshare(SmtTerm t, EliminateSharingContext context) {
    assert t != null;
    SmtTerm result = context.unshared.get(t);
    if (t.data != null) result = t;
    if (!t.sort().isSubsortOf(Sort.FORMULA)) result = t;
    for (SmtTerm c : t.children)
      if (!c.sort().isSubsortOf(Sort.FORMULA)) result = t;
    if (result != null) return result;

    ArrayList<SmtTerm> children = new ArrayList<SmtTerm>(t.children.size());
    for (SmtTerm c : t.children) children.add(unshare(c, context));
    result = context.term.mk(t.id, children);

    int S = getPrintSize(result, context);
    Integer P = context.parentCount.get(t);
    if (P == null) P = 0;
    if (S * P - S - P > 2) {
      String id = Id.get("plucked");
      context.varDefs.put(id, result);
      result = context.term.mk("var_formula", id);
    }

    context.unshared.put(t, result);
    return result;
  }
}
