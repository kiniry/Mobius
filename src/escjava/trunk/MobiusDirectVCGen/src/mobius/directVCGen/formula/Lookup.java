package mobius.directVCGen.formula;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import mobius.directVCGen.bico.IAnnotationGenerator;
import mobius.directVCGen.formula.PositionHint.MethodHint;
import mobius.directvcgen.vcgen.struct.Post;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.MethodGen;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * @author Herman Lehner (hermann.lehner@inf.ethz.ch)
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class Lookup {
  
  /** Defines whether 'null' can be returned or not. 
   *  If fFailSave is true, a default Term is returned
   *  instead of 'null' */
  private static final boolean fFailSave = true;
  
  /** an instance of the lookup object. */
  private static Lookup inst;
  
  
  /** map containing RoutineDecl as keys and Terms (the precondition) as value. **/
  private final Map<PositionHint, Term> fPreconditions = 
    new HashMap<PositionHint, Term>();

  /** map containing RoutineDecl as keys and Terms (the postcondition) as value. **/
  private final Map<PositionHint, Post> fPostconditions = 
    new HashMap<PositionHint, Post>();

  /** map containing RoutineDecl as keys and Terms (the exceptional postcondition) as value. */
  private final Map<PositionHint, Post> fExceptionalPostconditions = 
    new HashMap<PositionHint, Post>();

  
  /** the argument lists of each precondition. */
  private final Map<PositionHint, List<QuantVariableRef>> fPreArgs = 
    new HashMap<PositionHint, List<QuantVariableRef>>(); 
  /**  the argument lists of each precondition without the heap. */
  private final Map<PositionHint, List<QuantVariableRef>> fPreArgsWithoutHeap = 
    new HashMap<PositionHint, List<QuantVariableRef>>();

  /** map containing ClassDecl as keys and Terms (the invariant) as value. **/
  private final Map<JavaClass, Term> fInvariants = new HashMap<JavaClass, Term>();

  /** the current annotation generator which generates the informations
      of the lookup class. */
  private final IAnnotationGenerator fAnnotGen; 
  
  
  /**
   * Creates a new instance of the lookup, using the given annotation
   * generator.
   * @param gen an annotation generator
   */
  private Lookup(final IAnnotationGenerator gen) {
    fAnnotGen = gen;
  }
  
  /**
   * Initialize the lookup library with the proper annotation generator.
   * @param gen the annotation generator
   */
  public static void clear(final IAnnotationGenerator gen) {
    assert gen != null;
    inst = new Lookup(gen); 
  }
  
  /**
   * Returns the FOL Term representation of the precondition of method m.
   * @param m the method of interest
   * @return the precondition or <code>True</code>
   */
  public Term getPrecondition(final MethodGen m) {
    final PositionHint ph = PositionHint.getMethodPositionHint(m);
    Term t = fPreconditions.get(ph);
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
    final PositionHint ph = PositionHint.getMethodPositionHint(rd);
    final Term pOld = fPreconditions.get(ph);
    Term pNew;
    if (pOld == null) {
      pNew = term;
    }
    else {
      pNew = Logic.and(pOld, term);
    }
    fPreconditions.put(ph, pNew);
  }
  
  /**
   * Returns the FOL Term representation of the class invariant.
   * @param type the type to get the invariant from
   * @return the precondition or <code>True</code>
   */
  public Term getInvariant(final JavaClass type) {
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
  public void addInvariant(final JavaClass type, final Term term) {
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
   * Returns the FOL Term representation of the normal postcondition of routine m.
   * @param m the method of interest
   * @return the normal postcondition or <code>True</code>
   */
  public Post getNormalPostcondition(final MethodGen m) {
    //return new Post(buildStdCond (m, "_norm", true)); 
    final PositionHint ph = PositionHint.getMethodPositionHint(m);
    
    Post p = fPostconditions.get(ph);
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
    final PositionHint ph = PositionHint.getMethodPositionHint(rd);
    Post pNew = post;
    
    if (pNew == null && fFailSave) {
      pNew = new Post(Expression.rvar(Ref.sort), Logic.trueValue());
    }
    
    if (pNew != null && pNew.getRVar() == null && fFailSave) {
      pNew = new Post(Expression.rvar(Ref.sort), pNew);
    }
    
    final Post pOld = fPostconditions.get(ph);
    if (pOld != null) {
      // not the first time
      pNew = Post.and(pNew, pOld);
    }
    fPostconditions.put(ph, pNew);
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
    final PositionHint ph = PositionHint.getMethodPositionHint(m);
    Post p = fExceptionalPostconditions.get(ph);
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
    final PositionHint ph = PositionHint.getMethodPositionHint(rd);
    Post pNew = post;
    
    if (pNew == null && fFailSave) {
      pNew = new Post(Expression.rvar(Ref.sort), Logic.trueValue());
    }
    
    if (pNew != null && pNew.getRVar() == null && fFailSave) {
      pNew = new Post(Expression.rvar(Ref.sort), pNew);
    }
    
    final Post pOld = fExceptionalPostconditions.get(ph);
    if (pOld != null) {
      // not the first time
      pNew = Post.and(pNew, pOld);
    }
    fExceptionalPostconditions.put(ph, pNew);
  }


  /**
   * Adds a given Term to exceptional postconditions of a given method. 
   * @param rd the method
   * @param term fol term to be used as condition
   */
  public void addExceptionalPostcondition(final MethodGen rd, 
                                                 final Term term) {
    final PositionHint ph = PositionHint.getMethodPositionHint(rd);
    final Post pOld = fExceptionalPostconditions.get(ph);
    Post pNew;
    if (pOld == null) {
      pNew = new Post(Expression.rvar(Heap.sortValue), term);
    }
    else {
      pNew = Post.and(pOld, term);
    }
    fExceptionalPostconditions.put(ph, pNew);
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
    final List<MethodHint> lrout = new ArrayList<MethodHint>();
    lrout.add(PositionHint.getMethodPositionHint(rout));
    lrout.addAll(PositionHint.getMethodPositionList());
    
    for (MethodHint mp: lrout) {
      final List<QuantVariableRef> args = mkArguments(mp.getMethod());
      final LinkedList<QuantVariableRef> argsWithoutHeap = 
        new LinkedList<QuantVariableRef>();
      argsWithoutHeap.addAll(args);
      argsWithoutHeap.removeFirst();
      fPreArgs.put(mp, args);
      fPreArgsWithoutHeap.put(mp, argsWithoutHeap);
    }
    
  }
  
  /**
   * Returns the list of the arguments of the precondition.
   * Mostly, the heap, plus the arguments of the method.
   * @param m the method to get the precondition arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> getPreconditionArgs(final MethodGen m) {
    final PositionHint ph = PositionHint.getMethodPositionHint(m);
    //System.out.println(ph);
    return fPreArgs.get(ph);
  }
  
  
  /**
   * Returns the list of the arguments of the precondition,
   * without the heap. These are mainly the arguments of the method.
   * @param m the method to get the precondtion arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> getPreconditionArgsWithoutHeap(final MethodGen m) {
    final PositionHint ph = PositionHint.getMethodPositionHint(m);
    return fPreArgsWithoutHeap.get(ph);
  }
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    final String pre = "Preconditions: \n" +
                       "Arguments:" + fPreArgs + "\n" +
                       "Terms: " + fPreconditions + "\n";
    return pre;     
  }
  


  /**
   * Creates the arguments list of a method from its signature.
   * @param mg the method to get the arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> mkArguments(final MethodGen mg) {
    final List<QuantVariableRef> v = new Vector<QuantVariableRef>();
    
    final org.apache.bcel.generic.Type [] args = mg.getArgumentTypes();
    final List<String> names = fAnnotGen.getArgumentsName(mg);
    if (names.size() != args.length) {
      // TODO: change to a logger class
      System.err.println("There is an inconsistency between the " +
            "number of names and the number of variables for method " + mg + "!");
    }
    v.add(Heap.var);
    
    if (!mg.isStatic()) {
      v.add(Ref.varThis); 
    }
    
    int i = 0;
    for (org.apache.bcel.generic.Type typ: args) {
      v.add(Expression.rvar(names.get(i), Type.getSort(typ)));
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
  public Term[] getNormalPostconditionArgs(final MethodGen meth) {
    Term[] tab;
    final LinkedList<Term> args = new LinkedList<Term> ();
    args.add(Heap.varPre); 
    for (QuantVariableRef qvr: getPreconditionArgs(meth)) {
      if (!qvr.equals(Heap.var)) {
        args.add(Expression.old(qvr));
      }
      else {
        args.add(qvr);
      }
    }
    
    final QuantVariableRef qvr = Lookup.getInst().getNormalPostcondition(meth).getRVar();
    
    if (!Util.isVoid(meth)) {
      args.addFirst(Expression.normal(Expression.some(Heap.sortToValue(qvr))));
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
  public Term[] getExcPostconditionArgs(final MethodGen meth) {
    final Term[] tab = getNormalPostconditionArgs(meth);
    tab[0] = Expression.sym("Exception", 
                           new Term [] {getExceptionalPostcondition(meth).getRVar()});
    return tab;
  }
}
