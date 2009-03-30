package freeboogie.backend;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.logging.Logger;

/**
 * Builds a term tree, which looks like an S-expression.
 *
 * @author rgrig 
 */
public class SmtTermBuilder extends TermBuilder<SmtTerm> {
  private static final Logger log = Logger.getLogger("freeboogie.backend");
  private HashMap<String, SmtTerm> axioms = new HashMap<String, SmtTerm>();

  @Override
  protected SmtTerm reallyMk(Sort sort, String termId, Object a) {
    return SmtTerm.mk(sort, termId, a);
  }

  @Override
  protected SmtTerm reallyMk(Sort sort, String termId, ArrayList<SmtTerm> a) {
    return SmtTerm.mk(sort, termId, a);
  }

  @Override
  protected SmtTerm reallyMkNary(Sort sort, String termId, ArrayList<SmtTerm> a) {
    if (termId.equals("and") || termId.equals("or")) {
      boolean id = termId.equals("or") ? false : true;
      ArrayList<SmtTerm> children = new ArrayList<SmtTerm>(a.size());
      for (SmtTerm t : a) {
        if (t.id.equals(termId))
          children.addAll(t.children);
        else if (!t.id.equals("literal_formula") || (Boolean)t.data != id)
          children.add(t);
      }
      if (children.size() == 1)
        return children.get(0);
      if (children.size() == 0)
        return mk("literal_formula", id);
      a = children;
    }
    return SmtTerm.mk(sort, termId, a);
  }
}
