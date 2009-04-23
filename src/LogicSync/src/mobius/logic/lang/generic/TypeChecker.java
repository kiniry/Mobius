package mobius.logic.lang.generic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import mobius.logic.lang.generic.ast.Application;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.Clause;
import mobius.logic.lang.generic.ast.ClauseList;
import mobius.logic.lang.generic.ast.Evaluator;
import mobius.logic.lang.generic.ast.Forall;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;
import mobius.util.Logger;

public class TypeChecker {
  /** types id. */
  private final Set<String> t = new HashSet<String>();
  /** undeclared symbols. */
  private final Set<String> undeclared = new HashSet<String>();
  /** formulas. */
  private final Set<String> f = new HashSet<String>();

  private final HashMap<String, GType> symTypes = new HashMap<String, GType>();
  private final HashMap<Term, GType> termTypes = new HashMap<Term, GType>();

  private List<Entry<String, GType>> unknownTypes = new ArrayList<Entry<String, GType>> ();

  private final MyEvaluator evaluator = new MyEvaluator();
  private final GenericAst ast;
  private List<TypingError> errorList = new ArrayList<TypingError>();
  
  public TypeChecker(final GenericAst ast) {
    this.ast = ast;
  }
  
  public GType getType(String id) {
    return symTypes.get(id);
  }
 

 
  public boolean check() {
    return ast.eval(evaluator);
  }

  public void printDetailedResults() {
    if (unknownTypes.size() > 0) {
      Logger.err.println("\nType Checking failed because of the following not properly" +
                         " defined types.\n" + unknownTypes);
      Logger.err.flush();
    }
    Logger.out.println("Declared first order types: " + t);
    Logger.out.println("Undeclared first order types: " + undeclared);
    Logger.out.println("Collected formulas: " + f);
    Logger.out.println("Types: " + symTypes);
  }
  
  /**
   * Returns a string representing the given type.
   * @param term
   * @return
   */
  public String getType(Term term) {
    if (term instanceof Atom) {
      final String id = ((Atom) term).getId();
      if (id.equals("->")) {
        return "";
      }
    }
    final GType type = termTypes.get(term);
    if (type != null) {
      return "{" + type + "}";
    }
    return "";
  }
  private class MyEvaluator extends Evaluator<Boolean> { 
    
    private final LinkedList<Atom> forallVars = new LinkedList<Atom>();
    /** the current Id which is being inspected. */
    private String currClauseId;
    
    private Term getForallFirst(String id) {
      for (Atom at: forallVars) {
        if (at.getId().equals(id)) {
          return at;
        }
      }
      return null;
    }
    
    @Override
    public Boolean eval(final Application app, final Term next, final Term first) {
      first.eval(this);
      if (!(first instanceof Atom)) {
        errorList.add(new TypingError(currClauseId));
        return false;
      }
      final GType type = termTypes.get(first);
      
      if (type.isUnknown()) {
        type.setArity(GenericUtil.getArity(app));
      }
      Term curr = first.getNext();
      int i = 0;
      final Iterator<GType> titer = type.iterator();
      while (curr != null && titer.hasNext()) {
        if (!curr.eval(this)) {
          return false;
        }
        System.out.println(curr);
        final GType gt = titer.next();
        if (!gt.unifyElem(termTypes.get(curr))) {
          System.out.println("Failed to unify " + first + "(" + i + "): " + type + 
                             curr + ": " + termTypes.get(curr));
          return false;
        }
        curr = curr.getNext();
        i++;
      }
      if (curr != null) {
        System.out.println("Bad arity");
        return false;
      }
      termTypes.put(app, type.getReturn());
      
      return true;
    }
    
    
    @Override
    public Boolean eval(final Atom at, final Term next, final String id) {
      final Term orig = getForallFirst(id);
      if (orig != null) {          
        termTypes.put(at, termTypes.get(orig));
        return true;
      }
      return !isFormula(at);
      
    }
    @Override
    public Boolean eval(final ClauseList cl, final LinkedList<GenericAst> list) {
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
      
      // now we check that we don't have question mark type
      for (Entry<String, GType> e: symTypes.entrySet()) {
        if (e.getKey().equals("->") || e.getValue().getArity() == 1) {
          continue;
        }
        if (e.getValue().hasUnknown()) {
          
          unknownTypes.add(e);
        }
      }
      return unknownTypes.size() == 0;
    }


    @Override
    public Boolean eval(final Forall fall, final Term next, 
                        final Atom varlist, final Term term) {
      Atom curr = varlist;
      int i = 0;
      while (curr != null) {
        i++;
        forallVars.addFirst(curr);
        termTypes.put(curr, GType.getUnknown());
        curr = (Atom) curr.getNext();
      }
      if (!term.eval(this)) {
        return false;
      }
      while (i != 0) {
        forallVars.removeFirst();
        i--;
      }
      termTypes.put(fall, GType.getUnknown());
      return true;
    }

    @Override
    public Boolean eval(final Clause formula, final String id, final Term term) {
      currClauseId = id;
      final GType typ = checkType(term);
      if (typ != null) {
        t.add(id);
        symTypes.put(id, typ);
      }
      else {
        f.add(id);
      }
      if (!term.eval(this)) {
        return false;
      }
      return true;
    }
    
    
    
    
    private GType checkType(final Term term) {
      if (!(term instanceof Application)) {
        if (term instanceof Atom) {
          final Atom at = (Atom) term;
          if (!isFormula(at)) {
            return new GType(at.getId());
          }
        }
        return null;
      }
      final Application app = (Application) term;
      if (!GenericUtil.checkArity(app, 3)) {
        return null;
      }
      final Term first = app.getFirst();
      final Term snd = first.getNext();
      final Term thrd = snd.getNext();
      if (!(GenericUtil.isImplies(first)) ||
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
      type.addAll(rest);
      return type;
    }

    private boolean isFormula(Atom at) {
      final String id = at.getId();
      if (f.contains(id)) {
        // a formula
        return true;
      }
      if (t.contains(id)) {
        // it is an already known type
        termTypes.put(at, symTypes.get(id));
        return false;
      }
      // undeclared symbol
      symTypes.put(id, GType.getUnknown());
      termTypes.put(at, symTypes.get(id));
      undeclared.add(id);
      return false;
    }
  }
  public class TypingError {
    
    private String id;

    public TypingError(String id) {
      this.id = id;
    }
  }
  
}
