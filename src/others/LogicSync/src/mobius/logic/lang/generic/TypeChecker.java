package mobius.logic.lang.generic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
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
  /** types of the symbols. */
  private final Map<String, GType> symTypes = new HashMap<String, GType>();
  /** types of every single term of the ast. */
  private final Map<Term, GType> termTypes = new HashMap<Term, GType>();

  /** the visitor which type checks the ast. */
  private final MyEvaluator evaluator = new MyEvaluator();
  
  /** the ast which is being treated. */
  private final GenericAst ast;
  
  /** the list of errors detected during the typechecking. */
  private List<TypingError> errorList = new ArrayList<TypingError>();
  
  /** the types containing an unknown type sign. */
  private List<Entry<String, GType>> unknownTypes = new ArrayList<Entry<String, GType>> ();  

  public TypeChecker(final GenericAst ast) {
    this.ast = ast;
  }
  
  public GType getType(String id) {
    return symTypes.get(id);
  }
 

  /**
   * Typecheck the AST.
   * @return true if the typechecking succeeded
   */
  public boolean check() {
    return ast.eval(evaluator);
  }

  /**
   * Prints a verbose version of the result of the algorithm 
   * (better than yes or no).
   */
  public void printDetailedResults() {
    if (unknownTypes.size() > 0) {
      Logger.err.println("\nType Checking failed because of the following not properly" +
                         " defined types.\n" + unknownTypes);
      Logger.err.flush();
    }
    if (errorList.size() > 0) {
      final StringBuilder msg = new StringBuilder();
      msg.append("\nType Checking failed because of the following error(s):\n");
      for (TypingError err: errorList) {
        msg.append(err);
        msg.append("\n");
      }
      Logger.err.println(msg);
      Logger.err.flush();
    }
    Logger.out.println("Declared first order types: " + t);
    Logger.out.println("Undeclared first order types: " + undeclared);
    Logger.out.println("Collected formulas: " + f);
    Logger.out.println("Types: " + symTypes);
  }
  
  /**
   * Returns a string representing the given type.
   * The returned string is of the form { T } where T is the type
   * of the term. It returns an empty string in case of an implies.
   * @param term the term to get the type of, should not be null
   * @return a generic lang. commentary containing the type.
   */
  public String getType(final Term term) {
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

  public GType getTermType(final Term term) {
    return termTypes.get(term);
  }
  
  private class MyEvaluator extends Evaluator<Boolean> { 
    /** the list of variables declared by a forall. It is used like a Stack. */
    private final LinkedList<Atom> forallVars = new LinkedList<Atom>();
    /** the current Id which is being inspected. */
    private String currClauseId;
    
    /**
     * Returns the first variable which was declared in a forall having the
     * specified id.
     * @param id the name of a variable
     * @return the term declaration corresponding to the variable name,
     * otherwise null
     */
    private Term getForallFirst(final String id) {
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
        errorList.add(
          new TypingError(currClauseId, 
                          "The first member of an application should be an Atom! " +
                          "Found: " +
                          first + "."));
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
        //System.out.println(curr);
        final GType gt = titer.next();
        if (!gt.unifyElem(termTypes.get(curr))) {
          errorList.add(
              new UnifyingError(currClauseId, 
                              first, type, i, curr, termTypes.get(curr)));
          return false;
        }
        curr = curr.getNext();
        i++;
      }
      if (curr != null) {
        errorList.add(
             new TypingError(currClauseId, "Bad arity"));
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
          // oh yeah theres something rotten in the kingdom of Danemark
          // but we continue //failed to typecheck
          continue;
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
      return unknownTypes.size() == 0  && errorList.size() == 0;
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
    
    
    
    /**
     * Computes the type described by this term and returns
     * it if it is a valid type.
     * @param term the term to check
     * @return a valid type or null
     */
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
  
  
  public static class TypingError {
    
    private final String id;
    private final String msg;

    public TypingError(String id, String msg) {
      this.id = id;
      this.msg = msg;
    }
    
    @Override
    public String toString() {
      return id + ": " + msg;
    }
  }
  public static class UnifyingError extends TypingError {

    public UnifyingError(String id, Term first, GType typeFirst, int mem, 
                         Term curr, GType typeCurr) {
      super(id, "Failed to unify the member " + mem + " of "  + first + ": " + typeFirst + 
                           " with " + curr + ": " + typeCurr);
    }
    
  }
  
}
