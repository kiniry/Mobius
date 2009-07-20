package mobius.directVCGen.formula.annotation;

import java.util.ArrayList;
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
  
  /**
   * Construct an assertion around the given term.
   * @param name the name of the annotation
   * @param oldheap the name of the old heap variable used in the old cut
   * @param oldvars the array of the old variables where each variable has its
   * index corresponding to the index in the array
   * @param heap the name of the heap variable used in the cut
   * @param vars the array of the variables collected so far in the method
   * where the index of the variable corresponds to the index in the array
   * @param t the term which is the formula contained in 
   * the cut
   */
  public Cut(final String name, 
             final QuantVariableRef oldheap,
             final QuantVariableRef [] oldvars,
             final QuantVariableRef heap,
             final QuantVariableRef [] vars,
             final Term t) {
    this(name, new ArrayList<QuantVariableRef> (), t);
    final List<QuantVariableRef> l = getArgs();
    l.add(oldheap);
    for (QuantVariableRef qvr : oldvars) {
      l.add(qvr);
    }
    l.add(heap);
    for (QuantVariableRef qvr : vars) {
      l.add(qvr);
    }
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
