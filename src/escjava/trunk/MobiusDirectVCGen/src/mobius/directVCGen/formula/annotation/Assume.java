package mobius.directVCGen.formula.annotation;

import java.util.List;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * Represents an assume; 
 * for instance like <code>assume t</code>
 * which is translated in the vcs as: <code>t -> post</code>.
 * 
 * @author H. Lehner 
 */
public class Assume extends AAnnotation {
  /**
   * Construct an assume statement around the given term.
   * @param vars the arguments of the assume
   * @param name the name of the annotation
   * @param t the term which is the formula contained in 
   * the assume
   */
  public Assume(final String name, 
                final List<QuantVariableRef> vars, final Term t) {
    super(name, vars, t);
  }
  

  /**
   * {@inheritDoc}
   */
  @Override
  public int getID() {
    return annotAssume;
  }



}
