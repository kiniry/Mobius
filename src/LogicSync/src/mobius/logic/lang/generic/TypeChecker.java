package mobius.logic.lang.generic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import mobius.logic.lang.generic.ast.ACleanEvaluator;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;

public class TypeChecker extends ACleanEvaluator<Boolean> {
  private final Set<String> t = new HashSet<String>();
  private final Set<String> u = new HashSet<String>();
  private final Set<String> f = new HashSet<String>();
  private final GType Type = new GType("[T]");
  private final GType Unknown = new GType("[?]");
  private final HashMap<String, GType> types = new HashMap<String, GType>();
  @Override
  public Boolean evalApplication(Term next, Term first) {
    
    return checkType(first);
  }

  private boolean checkType(Term first) {
    if (first instanceof Atom) {
      final Atom a = (Atom) first;
      return (a.getId().equals("->") &&
              (a.getNext() instanceof Atom) &&
              (a.getNext().getNext().eval(this)));
    }
    return false;
  }

  @Override
  public Boolean evalAtom(Term next, String id) {
    if (f.contains(id)) {
      return false;
    }
    else if (t.contains(id)) {
      return true;
    }
    u.add(id);
    return true;
  }

  @Override
  public Boolean evalClauseList(final LinkedList<GenericAst> list) {
    for (GenericAst cl: list) {
      final boolean res = cl.eval(this);
      if (!res) {
        return false;
        // failed to typecheck
      }
    }
    return true;
  }

  @Override
  public Boolean evalDoc(final String content) {
    return true;
  }

  @Override
  public Boolean evalForall(Term next, Atom vars, Term term) {
    return false;
  }

  @Override
  public Boolean evalFormula(String id, Term term) {
    boolean res = term.eval(this);
    if (res) {
      t.add(id);
    }
    else {
      f.add(id);
    }
    return true;
  }

  @Override
  public Boolean evalSymbol(final String id) {
    if (t.contains(id)) {
      System.err.println(id + " is already defined!");
      return false;
    }
    t.add(id);
    types.put(id, Type);
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
    System.out.println("Types: " + types);
  }
  public static class GType {
    private List<String> type = new ArrayList<String>(); 
    public String toString() {
      StringBuilder blder = new StringBuilder();
      for (String t: type) {
        blder.append(" -> ");
        blder.append(t);
      }
      return blder.substring(" -> ".length());
    }
    public GType(String ...a) {
      for (String t: a) {
        type.add(t);
      }
    }
    
    public void add(String s) {
      type.add(s);
    }
  }
  
}
