package mobius.directVCGen.formula;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import javafe.ast.TypeDecl;
import mobius.directVCGen.bico.IMethProp;
import mobius.directVCGen.vcgen.struct.Post;

import org.apache.bcel.generic.MethodGen;

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
  private static Lookup inst = new Lookup();
  
  
  /** map containing RoutineDecl as keys and Terms (the precondition) as value. **/
  private Map<MethodGen, Term> preconditions = 
    new HashMap<MethodGen, Term>();

  /** map containing RoutineDecl as keys and Terms (the postcondition) as value. **/
  private Map<MethodGen, Post> postconditions = 
    new HashMap<MethodGen, Post>();

  /** map containing RoutineDecl as keys and Terms (the exceptional postcondition) as value. */
  private Map<MethodGen, Post> exceptionalPostconditions = 
    new HashMap<MethodGen, Post>();

  
  /** the argument lists of each precondition. */
  private final Map<MethodGen, List<QuantVariableRef>> fPreArgs = 
    new HashMap<MethodGen, List<QuantVariableRef>>(); 
  /**  the argument lists of each precondition without the heap. */
  private final Map<MethodGen, List<QuantVariableRef>> fPreArgsWithoutHeap = 
    new HashMap<MethodGen, List<QuantVariableRef>>(); 
  
  

  public static void clear() {
    inst = new Lookup();
    
  }
  
  /** map containing ClassDecl as keys and Terms (the invariant) as value. **/
  private final Map<TypeDecl, Term> fInvariants = new HashMap<TypeDecl, Term>();

  /** map containing ClassDecl as keys and Terms (the constraint) as value. **/
  private final Map<TypeDecl, Term> fConstraints = new HashMap<TypeDecl, Term>();

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
  public Term getPrecondition(final MethodGen m) {
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
  public void addPrecondition(final MethodGen rd, 
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
  public Post getNormalPostcondition(final MethodGen m) {
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
  public void addNormalPostcondition(final MethodGen rd, 
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
  public void addNormalPostcondition(final IMethProp mp, 
                                            final Term term) {
    final Post pOld = postconditions.get(mp.getBCELDecl());
    Post pNew;
    if (pOld == null) {
      if (mp.getResult() == null) {
        pNew = new Post(null, term);
      }
      else {
        pNew = new Post(mp.getResult(), term);
      }
    }
    else {
      pNew = Post.and(pOld, term);
    }
    postconditions.put(mp.getBCELDecl(), pNew);
  }
 
  
  /**
   * Returns a vector of FOL Term representations of the exceptional 
   * postconditions of method m.
   * The exceptional postcondition will always look like this: Sort => Term
   * @param m the method of interest
   * @return the exceptional postcondition or <code>True</code>
   */
  public Post getExceptionalPostcondition(final MethodGen m) {
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
  public void addExceptionalPostcondition(final MethodGen rd, 
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
  public void addExceptionalPostcondition(final MethodGen rd, 
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
  public void computePreconditionArgs(final MethodGen rout) {
    final List<MethodGen> lrout = new ArrayList<MethodGen>();
    lrout.addAll(preconditions.keySet());
    lrout.add(rout);
    
    for (MethodGen rd: lrout) {
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
  public List<QuantVariableRef> getPreconditionArgs(final MethodGen m) {
    return fPreArgs.get(m);
  }
  
  
  /**
   * Returns the list of the arguments of the precondition,
   * without the heap. These are mainly the arguments of the method.
   * @param m the method to get the precondtion arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> getPreconditionArgsWithoutHeap(final MethodGen m) {
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
  public List<QuantVariableRef> mkArguments(final MethodGen rd) {
    final List<QuantVariableRef> v = new Vector<QuantVariableRef>();
    
    final org.apache.bcel.generic.Type [] args = rd.getArgumentTypes();
    final String [] names = rd.getArgumentNames();
    
    v.add(Heap.var);
    
    if (!rd.isStatic()) {
      v.add(Ref.varThis); 
    }
    
    int i = 0;
    for (org.apache.bcel.generic.Type typ: args) {
      v.add(Expression.rvar(names[i], Type.getSort(typ)));
      i++;
    }
    return v;
  }

  /**
   * Returns a new array containing all the arguments of the
   * postcondition.
   * @param meth the method from which to compute the postcondition arguments
   * @return a newly created array
   */
  public static Term[] getNormalPostconditionArgs(final MethodGen meth) {
    Term[] tab;
    final LinkedList<Term> args = new LinkedList<Term> ();
    args.add(Heap.varPre); 
    for (QuantVariableRef qvr:Lookup.getInst().getPreconditionArgs(meth)) {
      if (!qvr.equals(Heap.var)) {
        args.add(Expression.old(qvr));
      }
      else {
        args.add(qvr);
      }
    }
    
    final QuantVariableRef qvr = Lookup.getInst().getNormalPostcondition(meth).getRVar();
    
    if (!Util.isVoid(meth)) {
      args.addFirst(Expression.normal(Expression.some(qvr)));
    }
    else {
      args.addFirst(Expression.normal(Expression.none()));
    }
    tab = args.toArray(new Term [args.size()]);
    return tab;
  }
  
  /**
   * Returns the arguments that will be used to instanciate an 
   * exceptionnal postcondition.
   * @param meth the method context
   * @return the array containing all the arguments.
   */
  public static Term[] getExcPostconditionArgs(final MethodGen meth) {
    final Term[] tab = getNormalPostconditionArgs(meth);
    tab[0] = Expression.sym("Exception", 
                           new Term [] {Lookup.getInst().getExceptionalPostcondition(meth).getRVar()});
    return tab;
  }
}
