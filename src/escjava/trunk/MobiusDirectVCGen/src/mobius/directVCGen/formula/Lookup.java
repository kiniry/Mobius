package mobius.directVCGen.formula;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.RoutineDecl;
import javafe.ast.TypeDecl;
import mobius.directVCGen.formula.jmlTranslator.struct.MethodProperties;
import mobius.directVCGen.vcgen.struct.Post;
import escjava.ast.Modifiers;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * @author hel
 *
 */
public class Lookup {
  
  /** Defines whether 'null' can be returned or not. 
   *  If fFailSave is true, a default Term is returned
   *  instead of 'null' */
  private static final boolean fFailSave = false;
  
  /** an instance of the lookup object. */
  private static final Lookup inst = new Lookup();
  
  
  /** map containing RoutineDecl as keys and Terms (the precondition) as value. **/
  private static Map<RoutineDecl, Term> preconditions = 
    new HashMap<RoutineDecl, Term>();

  /** map containing RoutineDecl as keys and Terms (the postcondition) as value. **/
  private static Map<RoutineDecl, Post> postconditions = 
    new HashMap<RoutineDecl, Post>();

  /** map containing RoutineDecl as keys and Terms (the exceptional postcondition) as value. */
  private static Map<RoutineDecl, Post> exceptionalPostconditions = 
    new HashMap<RoutineDecl, Post>();

  /** map containing ClassDecl as keys and Terms (the invariant) as value. **/
  private static Map<TypeDecl, Term> invariants = new HashMap<TypeDecl, Term>();

  /** map containing ClassDecl as keys and Terms (the constraint) as value. **/
  private static Map<TypeDecl, Term> constraints = new HashMap<TypeDecl, Term>();
  
  /** the argument lists of each precondition. */
  private final Map<RoutineDecl, List<QuantVariableRef>> fPreArgs = 
    new HashMap<RoutineDecl, List<QuantVariableRef>>(); 
  /**  the argument lists of each precondition without the heap. */
  private final Map<RoutineDecl, List<QuantVariableRef>> fPreArgsWithoutHeap = 
    new HashMap<RoutineDecl, List<QuantVariableRef>>(); 
  
  /**
   * Returns the FOL Term representation of the precondition of method m.
   * @param m the method of interest
   * @return the precondition or <code>True</code>
   */
  public static Term getInvariant(final TypeDecl type) {
    //return buildStdCond(m, "_pre", false);
    Term t = invariants.get(type);
    if (t == null) {
      t = Logic.True();
    }
    return t;
  }

  /**
   * Adds a given Term to precondition of a given method. 
   * @param rd the method
   * @param term fol term to be used as condition
   */
  public static void addInvariant(final TypeDecl type, 
                                            final Term term) {
    final Term pOld = invariants.get(type);
    Term pNew;
    if (pOld == null) {
      pNew = term;
    }
    else {
      pNew = Logic.and(pOld, term);
    }
    invariants.put(type, pNew);
  }
  
  /**
   * Returns the FOL Term representation of the precondition of method m.
   * @param m the method of interest
   * @return the precondition or <code>True</code>
   */
  public static Term getConstraint(final TypeDecl type) {
    //return buildStdCond(m, "_pre", false);
    Term t = constraints.get(type);
    if (t == null) {
      t = Logic.True();
    }
    return t;
  }

  /**
   * Adds a given Term to precondition of a given method. 
   * @param rd the method
   * @param term fol term to be used as condition
   */
  public static void addConstraint(final TypeDecl type, 
                                            final Term term) {
    final Term pOld = constraints.get(type);
    Term pNew;
    if (pOld == null) {
      pNew = term;
    }
    else {
      pNew = Logic.and(pOld, term);
    }
    constraints.put(type, pNew);
  }  
  
  /**
   * Returns the FOL Term representation of the precondition of method m.
   * @param m the method of interest
   * @return the precondition or <code>True</code>
   */
  public static Term getPrecondition(final RoutineDecl m) {
    //return buildStdCond(m, "_pre", false);
    Term t = preconditions.get(m);
    if (t == null) {
      t = Logic.True();
    }
    return t;
  }

  /**
   * Adds a given Term to precondition of a given method. 
   * @param rd the method
   * @param term fol term to be used as condition
   */
  public static void addPrecondition(final RoutineDecl rd, 
                                            final Term term) {
    final Term pOld = preconditions.get(rd);
    Term pNew;
    if (pOld == null) {
      pNew = term;
    }
    else {
      pNew = Logic.and(pOld, term);
    }
    preconditions.put(rd, pNew);
  }
  
  

  /**
   * Returns the FOL Term representation of the normal postcondition of routine m.
   * @param m the method of interest
   * @return the normal postcondition or <code>True</code>
   */
  public static Post getNormalPostcondition(final RoutineDecl m) {
    //return new Post(buildStdCond (m, "_norm", true)); 
    Post p = postconditions.get(m);
    if (p == null) {
      p = new Post(Logic.True());
    }
    return p;
  }

  /**
   * Adds a given Term to postconditions of a given method. 
   * @param rd the method
   * @param post to add to postconditions in Lookup hash map
   */
  public static void addNormalPostcondition(final RoutineDecl rd, 
                                            final Post post) {
    Post pNew = post;
    
    if (pNew == null && fFailSave) {
      pNew = new Post(Expression.rvar(Ref.sort), Logic.True());
    }
    
    if (pNew != null && pNew.getRVar() == null && fFailSave) {
      pNew = new Post(Expression.rvar(Ref.sort), pNew);
    }
    
    final Post pOld = postconditions.get(rd);
    if (pOld != null) {
      // not the first time
      pNew = Post.and(pNew, pOld);
    }
    postconditions.put(rd, pNew);
  }


  /**
   * Adds a given Term to postconditions of a given method. 
   * @param mp the method
   * @param term fol term to be used as condition
   */
  public static void addNormalPostcondition(final MethodProperties mp, 
                                            final Term term) {
    final Post pOld = postconditions.get(mp.fMethod);
    Post pNew;
    if (pOld == null) {
      if (mp.fResult == null){
        pNew = new Post(null, term);
      }
      else{
        pNew = new Post(mp.fResult, term);
      }
    }
    else {
      pNew = Post.and(pOld, term);
    }
    postconditions.put(mp.fMethod, pNew);
  }
 
  
  /**
   * Returns a vector of FOL Term representations of the exceptional 
   * postconditions of method m.
   * The exceptional postcondition will always look like this: Sort => Term
   * @param m the method of interest
   * @return the exceptional postcondition or <code>True</code>
   */
  public static Post getExceptionalPostcondition(final RoutineDecl m) {
    //return new Post(Expression.rvar(Ref.sort), buildStdCond (m, "_excp", false)); 
    Post p = exceptionalPostconditions.get(m);
    if (p == null) {
      p = new Post(Expression.rvar(Ref.sort), Logic.True());
    }
    return p;
  }

  /**
   * Adds a given Term to exceptional postconditions of a given method. 
   * @param rd the method
   * @param post to add to exceptional postconditions in Lookup hash map
   */
  public static void addExceptionalPostcondition(final RoutineDecl rd, 
                                                 final Post post) {
    Post pNew = post;
    
    if (pNew == null && fFailSave) {
      pNew = new Post(Expression.rvar(Ref.sort), Logic.True());
    }
    
    if (pNew != null && pNew.getRVar() == null && fFailSave) {
      pNew = new Post(Expression.rvar(Ref.sort), pNew);
    }
    
    final Post pOld = exceptionalPostconditions.get(rd);
    if (pOld != null) {
      // not the first time
      pNew = Post.and(pNew, pOld);
    }
    exceptionalPostconditions.put(rd, pNew);
  }


  /**
   * Adds a given Term to exceptional postconditions of a given method. 
   * @param rd the method
   * @param term fol term to be used as condition
   */
  public static void addExceptionalPostcondition(final RoutineDecl rd, 
                                                 final Term term) {
    final Post pOld = exceptionalPostconditions.get(rd);
    Post pNew;
    if (pOld == null) {
      pNew = new Post(Expression.rvar(Ref.sort), term);
    }
    else {
      pNew = Post.and(pOld, term);
    }
    exceptionalPostconditions.put(rd, pNew);
  }
  
  /**
   * Returns the current instance of the lookup object.
   * @return cannot be null
   */
  public static Lookup getInst() {
    return inst;
  }

  
  public void computePreconditionArgs() {
    if (fPreArgs.isEmpty()) {
      for (RoutineDecl rd: preconditions.keySet()) {
        final List<QuantVariableRef> args = mkArguments(rd);
        final LinkedList<QuantVariableRef> argsWithoutHeap = new LinkedList<QuantVariableRef>();
        argsWithoutHeap.addAll(args);
        argsWithoutHeap.removeFirst();
        fPreArgs.put(rd, args);
        fPreArgsWithoutHeap.put(rd, argsWithoutHeap);
      }
    }
  }
  
  public List<QuantVariableRef> getPreconditionArgs(final RoutineDecl m) {
    return fPreArgs.get(m);
  }
  public List<QuantVariableRef> getPreconditionArgsWithoutHeap(final RoutineDecl m) {
    return fPreArgsWithoutHeap.get(m);
  }
  /**
   * @return the content of the object
   */
  @Override
  public String toString() {
    final String pre = "Preconditions: \n" +
                       "Arguments:" + fPreArgs + "\n" +
                       "Terms: " + preconditions + "\n";
    return pre;
           
  }
  
  public static List<QuantVariableRef> mkArguments(final RoutineDecl rd) {
    final List<QuantVariableRef> v = new Vector<QuantVariableRef>();
    final FormalParaDeclVec fpdvec = rd.args;
    v.add(Heap.var);
    if (Modifiers.isStatic(rd.modifiers)) {
      v.add(Ref.varThis); 
    }
    final FormalParaDecl[] args = fpdvec.toArray();
    for (FormalParaDecl fpd: args) {
      v.add(Expression.rvar(fpd));
    }
    return v;
  }
}
