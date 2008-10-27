package mobius.directVCGen.translator;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javafe.ast.RoutineDecl;
import javafe.ast.TypeDecl;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.MethodGetter;
import mobius.directVCGen.translator.struct.MethodProperties;
import mobius.directVCGen.vcgen.struct.Post;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

class LookupJavaFe {
  
  /** an instance of the lookup object. */
  private static LookupJavaFe inst = new LookupJavaFe();
  
  /** map containing ClassDecl as keys and Terms (the constraint) as value. **/
  private final Map<TypeDecl, Term> fConstraints = new HashMap<TypeDecl, Term>();

  /** map containing ClassDecl as keys and Terms (the invariant) as value. **/
  private final Map<TypeDecl, Term> fInvariants = new HashMap<TypeDecl, Term>();


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
   * Returns the current instance of the lookup object.
   * @return cannot be null
   */
  public static LookupJavaFe getInst() {
    return inst;
  }

  
  /**
   * Adds a given Term to precondition of a given method. 
   * @param rd the method
   * @param term fol term to be used as condition
   */
  public void addPrecondition(final RoutineDecl rd, 
                              final Term term) {
    Lookup.getInst().addPrecondition(MethodGetter.translate(rd), term);
  }
  
  /**
   * Adds a given Term to postconditions of a given method. 
   * @param rd the method
   * @param post to add to postconditions in Lookup hash map
   */
  public void addNormalPostcondition(final RoutineDecl rd, 
                                            final Post post) {
    Lookup.getInst().addNormalPostcondition(MethodGetter.translate(rd), post);
  }
  
  
  /**
   * Adds a given Term to exceptional postconditions of a given method. 
   * @param rd the method
   * @param post to add to exceptional postconditions in Lookup hash map
   */
  public void addExceptionalPostcondition(final RoutineDecl rd, 
                                                 final Post post) {
    Lookup.getInst().addExceptionalPostcondition(MethodGetter.translate(rd), post);
  }


  /**
   * Adds a given Term to exceptional postconditions of a given method. 
   * @param rd the method
   * @param term fol term to be used as condition
   */
  public void addExceptionalPostcondition(final RoutineDecl rd, 
                                                 final Term term) {
    Lookup.getInst().addExceptionalPostcondition(MethodGetter.translate(rd), term); 
  }
  
  
  /**
   * Returns the list of the arguments of the precondition.
   * Mostly, the heap, plus the arguments of the method.
   * @param m the method to get the precondition arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> getPreconditionArgs(final RoutineDecl m) {
    return Lookup.getInst().getPreconditionArgs(MethodGetter.translate(m));
  }
  public Post getNormalPostcondition(final RoutineDecl m) {
    return Lookup.getInst().getNormalPostcondition(MethodGetter.translate(m));
  }
  
  /**
   * Returns a vector of FOL Term representations of the exceptional 
   * postconditions of method m.
   * The exceptional postcondition will always look like this: Sort => Term
   * @param m the method of interest
   * @return the exceptional postcondition or <code>True</code>
   */
  public Post getExceptionalPostcondition(final RoutineDecl m) {
    return Lookup.getInst().getExceptionalPostcondition(MethodGetter.translate(m));
  }
  /**
   * Creates the arguments list of a method from its signature.
   * @param rd the method to get the arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> mkArguments(final RoutineDecl rd) {
    return Lookup.getInst().mkArguments(MethodGetter.translate(rd));
  }

  public Term[] getNormalPostconditionArgs(RoutineDecl meth) {

    return Lookup.getInst().getNormalPostconditionArgs(MethodGetter.translate(meth));
  }

  public Term[] getExcPostconditionArgs(RoutineDecl meth) {

    return Lookup.getInst().getExcPostconditionArgs(MethodGetter.translate(meth));
  }
  
  /**
   * Returns the FOL Term representation of the precondition of method m.
   * @param m the method of interest
   * @return the precondition or <code>True</code>
   */
  public Term getPrecondition(final RoutineDecl m) {
    return Lookup.getInst().getPrecondition(MethodGetter.translate(m));
  }
  
  /**
   * Adds a given Term to postconditions of a given method. 
   * @param mp the method
   * @param term fol term to be used as condition
   */
  public void addNormalPostcondition(final MethodProperties mp, 
                                            final Term term) {
    Post pNew;
    if (mp.getResult() == null) {
      pNew = new Post(null, term);
    }
    else {
      pNew = new Post(mp.getResult(), term);
    }   
    Lookup.getInst().addNormalPostcondition(mp.getBCELDecl(), pNew); 
  }
} 
