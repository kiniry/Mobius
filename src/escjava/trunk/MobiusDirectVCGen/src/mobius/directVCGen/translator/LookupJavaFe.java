package mobius.directVCGen.translator;

import java.util.List;

import javafe.ast.RoutineDecl;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.vcgen.struct.Post;

import org.apache.bcel.generic.MethodGen;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

class LookupJavaFe extends Lookup {
  
  
  /** an instance of the lookup object. */
  private static LookupJavaFe inst = new LookupJavaFe();
  


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
    addPrecondition(translate(rd), term);
  }
  
  /**
   * Adds a given Term to postconditions of a given method. 
   * @param rd the method
   * @param post to add to postconditions in Lookup hash map
   */
  public void addNormalPostcondition(final RoutineDecl rd, 
                                            final Post post) {
    addNormalPostcondition(translate(rd), post);
  }
  
  
  /**
   * Adds a given Term to exceptional postconditions of a given method. 
   * @param rd the method
   * @param post to add to exceptional postconditions in Lookup hash map
   */
  public void addExceptionalPostcondition(final RoutineDecl rd, 
                                                 final Post post) {
    addExceptionalPostcondition(translate(rd), post);
  }


  /**
   * Adds a given Term to exceptional postconditions of a given method. 
   * @param rd the method
   * @param term fol term to be used as condition
   */
  public void addExceptionalPostcondition(final RoutineDecl rd, 
                                                 final Term term) {
    addExceptionalPostcondition(translate(rd), term); 
  }
  
  
  /**
   * Returns the list of the arguments of the precondition.
   * Mostly, the heap, plus the arguments of the method.
   * @param m the method to get the precondition arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> getPreconditionArgs(final RoutineDecl m) {
    return getPreconditionArgs(translate(m));
  }
  public Post getNormalPostcondition(final RoutineDecl m) {
    return getNormalPostcondition(translate(m));
  }
  
  /**
   * Returns a vector of FOL Term representations of the exceptional 
   * postconditions of method m.
   * The exceptional postcondition will always look like this: Sort => Term
   * @param m the method of interest
   * @return the exceptional postcondition or <code>True</code>
   */
  public Post getExceptionalPostcondition(final RoutineDecl m) {
    return getExceptionalPostcondition(translate(m));
  }
  /**
   * Creates the arguments list of a method from its signature.
   * @param rd the method to get the arguments from
   * @return a list of variables
   */
  public List<QuantVariableRef> mkArguments(final RoutineDecl rd) {
    return mkArguments(translate(rd));
  }

  public Term[] getNormalPostconditionArgs(RoutineDecl meth) {

    return getNormalPostconditionArgs(translate(meth));
  }

  public Term[] getExcPostconditionArgs(RoutineDecl meth) {

    return getExcPostconditionArgs(translate(meth));
  }
  
  /**
   * Returns the FOL Term representation of the precondition of method m.
   * @param m the method of interest
   * @return the precondition or <code>True</code>
   */
  public Term getPrecondition(final RoutineDecl m) {
    return getPrecondition(translate(m));
  }
} 
