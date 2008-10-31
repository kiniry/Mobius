package mobius.directVCGen.formula;

import java.util.List;

import escjava.sortedProver.Lifter.QuantVariableRef;

/**
 * An interface used to give hints at the creation of annotations.
 * The hint have informations depending on the location of the 
 * annotations.
 * 
 * @see mobius.directVCGen.formula.annotation.Assert
 * @see mobius.directVCGen.formula.annotation.Cut
 * @see mobius.directVCGen.formula.annotation.Assume
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public interface ILocalVars {
  /**
   * Returns the list of local variables at the current program point,
   * where the annotation is located.
   * 
   * 
   * @return a list of variable, never null
   */
  List<QuantVariableRef> getLocalVars(); 
  
  /**
   * Returns the list of arguments of the currently inspected method,
   * where the annotation is located.
   * 
   * @return a list of variable, never null
   */
  List<QuantVariableRef> getArgs();
}
