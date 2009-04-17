package mobius.logic.lang.generic;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;
import java.util.Stack;

import mobius.logic.lang.generic.ast.Application;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.ClauseList;
import mobius.logic.lang.generic.ast.Evaluator;
import mobius.logic.lang.generic.ast.Forall;
import mobius.logic.lang.generic.ast.Formula;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Symbol;
import mobius.logic.lang.generic.ast.Term;

public class TypeChecker extends Evaluator<Boolean> {
  private final Set<String> t = new HashSet<String>();
  private final Set<String> u = new HashSet<String>();
  private final Set<String> f = new HashSet<String>();
  private final GType Type = new GType("[T]");
  private final HashMap<String, GType> symTypes = new HashMap<String, GType>();
  private final HashMap<String, GType> termTypes = new HashMap<String, GType>();
  private final Set<Term> forallVars = new HashSet<Term>();
  private final Stack<String> vars = new Stack<String>();
  
  @Override
  public Boolean eval(Application app, Term next, Term first) {
    

    first.eval(this);
    if (!(first instanceof Atom)) {
      System.err.println("I am suspicious about: " + first);
   
    }
    GType type = termTypes.get(first);
    if (type.isUnknown()) {
      type.setArity(getArity(app));
    }
    Term curr = first.getNext();
    int i = 0;
    while (curr != null) {
      curr.eval(this);
      type = type.unify(i, termTypes.get(curr));
      curr = curr.getNext();
      i++;
    }
    
    
    return false;
  }

  private GType checkType(final Term term) {
    if (!(term instanceof Application)) {
      if (term instanceof Atom) {
        final Atom at = (Atom) term;
        if (at.eval(this)) {
          return new GType(at.getId());
        }
      }
      return null;
    }
    final Application app = (Application) term;
    if (!checkArity(app, 3)) {
      return null;
    }
    final Term first = app.getFirst();
    final Term snd = first.getNext();
    final Term thrd = snd.getNext();
    if (!(isImplies(first)) ||
        !(snd instanceof Atom) ||
        !((thrd instanceof Application) ||
            (thrd instanceof Atom))) {
      return null;
    }

    final GType type = checkType(snd);
    final GType rest = checkType(thrd);
    if (type == null || rest == null) {
      return null;
    }
    type.add(rest);
    return type;
  }

  private boolean isImplies(Term first) {
    if (!(first instanceof Atom)) {
      return false;
    }
    final Atom imp = (Atom) first;
    return imp.getId().equals("->");
  }

  private boolean checkArity(Application app, int arity) {
    return getArity(app) == arity;
  }
  private int getArity(Application app) {
    Term curr = app.getFirst();
    int cnt = 0;
    while (curr != null) {
      cnt++;
      curr = curr.getNext();
    }
    return cnt;
  }
  @Override
  public Boolean eval(Atom at, Term next, String id) {
    if (f.contains(id)) {
      return false;
    }
    else {
      if (t.contains(id)) {
        return true;
      }
      symTypes.put(id, GType.getUnknown());
      u.add(id);
      return true;
    }
  }

  @Override
  public Boolean eval(ClauseList cl, final LinkedList<GenericAst> list) {
    for (GenericAst c: list) {
      
      final Boolean res = c.eval(this);
      if (res == null) {
        continue;
      }
      if (!res) {
        return false;
        // failed to typecheck
      }
    }
    return true;
  }


  @Override
  public Boolean eval(Forall fall, Term next, 
                      Atom varlist, Term term) {
    Atom curr = varlist;
    int i = 0;
    while (curr != null) {
      i++;
      vars.push(curr.getId());
      curr = (Atom) curr.getNext();
    }
    term.eval(this);
    while (i != 0) {
      vars.pop();
      i--;
    }
    return false;
  }

  @Override
  public Boolean eval(Formula formula, String id, Term term) {
    final GType typ = checkType(term);
    if (typ != null) {
      t.add(id);
      symTypes.put(id, typ);
    }
    else {
      f.add(id);
    }
    term.eval(this);
    return true;
  }

  @Override
  public Boolean eval(Symbol s, final String id) {
    if (t.contains(id)) {
      System.err.println(id + " is already defined!");
      return false;
    }
    t.add(id);
    symTypes.put(id, Type);
    return true;
  }

  public static boolean check(GenericAst ast) {
    final TypeChecker tc = new TypeChecker();
    return ast.eval(tc);
  }

  public void printDetailedResults() {
    System.out.println("Declared first order types: " + t);
    System.out.println("Undeclared first order types: " + u);
    System.out.println("Collected formulas: " + f);
    System.out.println("Types: " + symTypes);
  }
  public String getType(Term term) {
    if (term instanceof Atom) {
      String id = ((Atom) term).getId();
      if (id.equals("->")) {
        return "";
      }
      GType type = symTypes.get(id);
      if (type != null) {
        return "{" + type + "}";
      }
    }
    return "";
  }
  
}
