package mobius.directvcgen.translator;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.bcel.generic.MethodGen;

import javafe.ast.RoutineDecl;
import javafe.ast.TypeDecl;
import javafe.tc.TypeSig;
import mobius.directvcgen.formula.Logic;
import mobius.directvcgen.formula.Lookup;
import mobius.directvcgen.formula.Translator;
import mobius.directvcgen.translator.struct.MethodProperties;
import mobius.directvcgen.vcgen.struct.Post;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;


/**
 * A lookup class specific to JavaFE; using specific JavaFE structures.
 * 
 * @see mobius.directvcgen.formula.Lookup
 * @author J. Charles (julien.charles@inria.fr)
 */
class LookupJavaFe {
  
  /** an instance of the lookup object. */
  private static LookupJavaFe inst = new LookupJavaFe();
  
  /** map containing ClassDecl as keys and Terms (the constraint) as value. **/
  private final Map<TypeDecl, Term> fConstraints = new HashMap<TypeDecl, Term>();


  /**
   * Returns the FOL Term representation of the class invariant.
   * @param type the type to get the invariant from
   * @return the precondition or <code>True</code>
   */
  public Term getInvariant(final TypeDecl type) {
    
    return Lookup.getInst().getInvariant(Translator.getInst().translate(TypeSig.getSig(type)));
  }
  

  /**
   * Adds a given Term to the invariant of a given class. 
   * @param type the type
   * @param term fol term to be used as condition
   */
  public void addInvariant(final TypeDecl type, final Term term) {
    Lookup.getInst().addInvariant(Translator.getInst().translate(TypeSig.getSig(type)), term);
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
    Lookup.getInst().addPrecondition(Translator.getInst().translate(rd), term);
  }
  
  /**
   * Adds a given Term to postconditions of a given method. 
   * @param rd the method
   * @param post to add to postconditions in Lookup hash map
   */
  public void addNormalPostcondition(final RoutineDecl rd, 
                                            final Post post) {
    Lookup.getInst().addNormalPostcondition(Translator.getInst().translate(rd), post);
  }
  
  
  /**
   * Adds a given Term to exceptional postconditions of a given method. 
   * @param rd the method
   * @param post to add to exceptional postconditions in Lookup hash map
   */
  public void addExceptionalPostcondition(final RoutineDecl rd, 
                                                 final Post post) {
    Lookup.getInst().addExceptionalPostcondition(Translator.getInst().translate(rd), post);
  }


  /**
   * Adds a given Term to exceptional postconditions of a given method. 
   * @param rd the method
   * @param term fol term to be used as condition
   */
  public void addExceptionalPostcondition(final RoutineDecl rd, 
                                                 final Term term) {
    Lookup.getInst().addExceptionalPostcondition(Translator.getInst().translate(rd), term); 
  }
  
  
  /**
   * Returns the list of the arguments of the precondition.
   * Mostly, the heap, plus the arguments of the method.
   * @param m the method to get the precondition arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> getPreconditionArgs(final RoutineDecl m) {
    return Lookup.getInst().getPreconditionArgs(Translator.getInst().translate(m));
  }
  
  /**
   * Returns the FOL Term representation of the normal postcondition of routine m.
   * @param m the method of interest
   * @return the normal postcondition or <code>True</code>
   */
  public Post getNormalPostcondition(final RoutineDecl m) {
    return Lookup.getInst().getNormalPostcondition(Translator.getInst().translate(m));
  }
  
  /**
   * Returns a vector of FOL Term representations of the exceptional 
   * postconditions of method m.
   * The exceptional postcondition will always look like this: Sort => Term
   * @param m the method of interest
   * @return the exceptional postcondition or <code>True</code>
   */
  public Post getExceptionalPostcondition(final RoutineDecl m) {
    return Lookup.getInst().getExceptionalPostcondition(Translator.getInst().translate(m));
  }
  /**
   * Creates the arguments list of a method from its signature.
   * @param rd the method to get the arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> mkArguments(final RoutineDecl rd) {
    return Lookup.getInst().mkArguments(Translator.getInst().translate(rd));
  }
  
  /**
   * Returns a new array containing all the arguments of the
   * postcondition.
   * @param meth the method from which to compute the postcondition arguments
   * @return a newly created array
   */
  public Term[] getNormalPostconditionArgs(final RoutineDecl meth) {

    return Lookup.getInst().getNormalPostconditionArgs(Translator.getInst().translate(meth));
  }

  /**
   * Returns the arguments that will be used to instanciate an 
   * exceptionnal postcondition.
   * @param meth the method context
   * @return the array containing all the arguments.
   */
  public Term[] getExcPostconditionArgs(final RoutineDecl meth) {

    return Lookup.getInst().getExcPostconditionArgs(Translator.getInst().translate(meth));
  }
  
  /**
   * Returns the FOL Term representation of the precondition of method m.
   * @param m the method of interest
   * @return the precondition or <code>True</code>
   */
  public Term getPrecondition(final RoutineDecl m) {
    return Lookup.getInst().getPrecondition(Translator.getInst().translate(m));
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
    final MethodGen mg = Translator.getInst().translate(mp.getDecl());
    Lookup.getInst().addNormalPostcondition(mg, pNew); 
  }
} 
