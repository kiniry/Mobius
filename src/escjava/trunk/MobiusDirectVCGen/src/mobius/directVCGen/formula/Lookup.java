package mobius.directVCGen.formula;

import java.util.ArrayList;
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
 * @author Herman Lehner (hermann.lehner@inf.ethz.ch)
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
  private final Map<TypeDecl, Term> fInvariants = new HashMap<TypeDecl, Term>();

  /** map containing ClassDecl as keys and Terms (the constraint) as value. **/
  private final Map<TypeDecl, Term> fConstraints = new HashMap<TypeDecl, Term>();
  
  /** the argument lists of each precondition. */
  private final Map<RoutineDecl, List<QuantVariableRef>> fPreArgs = 
    new HashMap<RoutineDecl, List<QuantVariableRef>>(); 
  /**  the argument lists of each precondition without the heap. */
  private final Map<RoutineDecl, List<QuantVariableRef>> fPreArgsWithoutHeap = 
    new HashMap<RoutineDecl, List<QuantVariableRef>>(); 
  
  /**
   * Returns the FOL Term representation of the class invariant.
   * @param type the type to get the invariant from
   * @return the precondition or <code>True</code>
   */
  public Term getInvariant(final TypeDecl type) {
    Term t = fInvariants.get(type);
    if (t == null) {
      t = Logic.trueValue();
    }
    return t;
  }
  
  

  /**
   * Adds a given Term to the invariant of a given class. 
   * @param type the type
   * @param term fol term to be used as condition
   */
  public void addInvariant(final TypeDecl type, final Term term) {
    final Term pOld = fInvariants.get(type);
    Term pNew;
    if (pOld == null) {
      pNew = term;
    }
    else {
      pNew = Logic.and(pOld, term);
    }
    fInvariants.put(type, pNew);
  }
  
  /**
   * Returns the FOL Term representation of the constraints of a given class.
   * @param type the class which we want to get the constraints from
   * @return the precondition or <code>True</code>
   */
  public Term getConstraint(final TypeDecl type) {
    //return buildStdCond(m, "_pre", false);
    Term t = fConstraints.get(type);
    if (t == null) {
      t = Logic.trueValue();
    }
    return t;
  }

  /**
   * Adds a given Term to the constraints of a given class.
   * @param type the class targeted
   * @param term fol term to be used as constraint
   */
  public void addConstraint(final TypeDecl type, 
                            final Term term) {
    final Term pOld = fConstraints.get(type);
    Term pNew;
    if (pOld == null) {
      pNew = term;
    }
    else {
      pNew = Logic.and(pOld, term);
    }
    fConstraints.put(type, pNew);
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
      t = Logic.trueValue();
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
      p = new Post(Logic.trueValue());
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
      pNew = new Post(Expression.rvar(Ref.sort), Logic.trueValue());
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
    final Post pOld = postconditions.get(mp.getDecl());
    Post pNew;
    if (pOld == null) {
      if (mp.fResult == null) {
        pNew = new Post(null, term);
      }
      else {
        pNew = new Post(mp.fResult, term);
      }
    }
    else {
      pNew = Post.and(pOld, term);
    }
    postconditions.put(mp.getDecl(), pNew);
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
      p = new Post(Expression.rvar(Heap.sortValue), Logic.trueValue());
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
      pNew = new Post(Expression.rvar(Ref.sort), Logic.trueValue());
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
      pNew = new Post(Expression.rvar(Heap.sortValue), term);
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

  /**
   * Compute the precondition arguments. The call to this method should be done only
   * once for each method.
   * @param rout the method to compute the arguments for
   */
  public void computePreconditionArgs(final RoutineDecl rout) {
    final List<RoutineDecl> lrout = new ArrayList<RoutineDecl>();
    lrout.addAll(preconditions.keySet());
    lrout.add(rout);
    
    for (RoutineDecl rd: lrout) {
      final List<QuantVariableRef> args = mkArguments(rd);
      final LinkedList<QuantVariableRef> argsWithoutHeap = 
        new LinkedList<QuantVariableRef>();
      argsWithoutHeap.addAll(args);
      argsWithoutHeap.removeFirst();
      fPreArgs.put(rd, args);
      fPreArgsWithoutHeap.put(rd, argsWithoutHeap);
    }
    
  }
  
  /**
   * Returns the list of the arguments of the precondition.
   * Mostly, the heap, plus the arguments of the method.
   * @param m the method to get the precondition arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> getPreconditionArgs(final RoutineDecl m) {
    return fPreArgs.get(m);
  }
  
  
  /**
   * Returns the list of the arguments of the precondition,
   * without the heap. These are mainly the arguments of the method.
   * @param m the method to get the precondtion arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> getPreconditionArgsWithoutHeap(final RoutineDecl m) {
    return fPreArgsWithoutHeap.get(m);
  }
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    final String pre = "Preconditions: \n" +
                       "Arguments:" + fPreArgs + "\n" +
                       "Terms: " + preconditions + "\n";
    return pre;     
  }
  
  /**
   * Creates the arguments list of a method from its signature.
   * @param rd the method to get the arguments from
   * @return a list of variables
   */
  public static List<QuantVariableRef> mkArguments(final RoutineDecl rd) {
    final List<QuantVariableRef> v = new Vector<QuantVariableRef>();
    final FormalParaDeclVec fpdvec = rd.args;
    v.add(Heap.var);
    if (!Modifiers.isStatic(rd.modifiers)) {
      v.add(Ref.varThis); 
    }
    final FormalParaDecl[] args = fpdvec.toArray();
    for (FormalParaDecl fpd: args) {
      v.add(Expression.rvar(fpd));
    }
    return v;
  }
}
