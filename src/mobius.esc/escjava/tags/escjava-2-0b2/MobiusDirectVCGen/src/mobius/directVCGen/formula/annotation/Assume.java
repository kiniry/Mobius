package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;

/**
 * Represents an assume; 
 * for instance like <code>assume t</code>
 * which is translated in the vcs as: <code>t -> post</code>.
 */
public class Assume extends AAnnotation {
  /**
   * Construct an assume statement around the given term.
   * @param t the term which is the formula contained in 
   * the assume
   */
  public Assume(final Term t) {
    super(t);
  }
  
  /*
   * (non-Javadoc)
   * @see mobius.directVCGen.formula.annotation.AAnnotation#getID()
   */
  @Override
  public int getID() {
    return annotAssume;
  }



}
