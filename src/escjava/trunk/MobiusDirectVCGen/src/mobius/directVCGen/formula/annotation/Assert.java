package mobius.directVCGen.formula.annotation;

import java.util.List;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * Represents an assert; 
 * for instance like <code>assert t</code>
 * which is translated in the vcs as:  <code>t</code>, <code>t -> post</code>.
 * @author H. Lehner and J. Charles (julien.charles@inria.fr)
 */
public class Assert extends AAnnotation {
  /**
   * Constructor that takes one argument, the term contained in the
   * assert.
   * @param name the name of the assertion
   * @param args the arguments of the annotation
   * @param t the term of the assert, should not be <code>null</code>
   */
  public Assert(final String name, 
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
    return annotAssert;
  }



}
