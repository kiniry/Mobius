package mobius.directVCGen.formula.annotation;

import java.util.List;

import escjava.sortedProver.Lifter.QuantVariableRef;
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
  public Cut(final String name, 
                final List<QuantVariableRef> args, 
                final Term t) {
    super(name, args, t);
    if (t == null) {
      throw new NullPointerException();
    }
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
