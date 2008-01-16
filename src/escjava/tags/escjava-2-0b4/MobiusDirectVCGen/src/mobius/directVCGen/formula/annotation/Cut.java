package mobius.directVCGen.formula.annotation;

import java.util.List;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * Represents a cut; 
 * for instance like <code>cut t</code>
 * which is translated in the vcs as: <code>t /\ (t -> post)</code>.
 * @author H. Lehner and J. Charles (julien.charles@inria.fr)
 */
public class Cut extends AAnnotation {
  /**
   * Construct an cut statement around the given term.
   * @param name the name of the annotation
   * @param args the arguments of the annotation
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

  /** {@inheritDoc} */
  @Override
  public int getID() {
    return annotCut;
  }



}
