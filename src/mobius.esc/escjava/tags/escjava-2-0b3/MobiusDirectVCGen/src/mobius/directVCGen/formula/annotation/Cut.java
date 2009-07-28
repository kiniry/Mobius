package mobius.directVCGen.formula.annotation;

import escjava.sortedProver.Lifter.Term;

/**
 * Represents a cut; 
 * for instance like <code>cut t</code>
 * which is translated in the vcs as: <code>t /\ (t -> post)</code>.
 */
public class Cut extends AAnnotation {
  /**
   * Construct an cut statement around the given term.
   * @param t the term which is the formula contained in 
   * the cut
   */
  public Cut(final Term t) {
    super(t);
  }
  
  /*
   * (non-Javadoc)
   * @see mobius.directVCGen.formula.annotation.AAnnotation#getID()
   */
  @Override
  public int getID() {
    return annotCut;
  }



}
