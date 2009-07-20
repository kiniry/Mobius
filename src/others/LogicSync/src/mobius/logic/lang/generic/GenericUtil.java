package mobius.logic.lang.generic;

import mobius.logic.lang.generic.ast.Application;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.Term;

public class GenericUtil {
  public static boolean isImplies(Term first) {
    if (!(first instanceof Atom)) {
      return false;
    }
    final Atom imp = (Atom) first;
    return imp.getId().equals("->");
  }

  public static boolean checkArity(Application app, int arity) {
    return getArity(app) == arity;
  }
  public static int getArity(Application app) {
    Term curr = app.getFirst();
    int cnt = 0;
    while (curr != null) {
      cnt++;
      curr = curr.getNext();
    }
    return cnt;
  }
}
