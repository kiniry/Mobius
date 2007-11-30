package mobius.directVCGen.formula;

import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.Lifter;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.STerm;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * This is the library class for generic handling of the formulas.
 * It is not used to create terms. The sort attached to it
 * is the sort any... But it should not be used (yes - it is
 * marked as deprecated).
 * @author J. Charles (julien.charles@inria.fr), H. Lehner
 */
public final class Formula {

  /** the current instance of the lifter: used to build the formulas. */
  static Lifter lf = new Lifter(new CoqNodeBuilder());

  /** 
   * the sort that represents any sort... should not be used.
   * @deprecated use any other sort from any other library
   */
  private static final Sort sortAny = lf.sortAny;
  
  

  /**
   * @deprecated
   */
  private Formula() {
    
  }
  
  /**
   * Generate the formulas from a given term using the
   * current lifter.
   * @param t The terms to translate
   * @return the formulas ready to be dumped
   */
  public static STerm generateFormulas(final Term t) {
    lf.dumpBuilder = lf.builder;
    final STerm st = t.dump();
    lf.dumpBuilder = null;
    return st;
  }

  /**
   * Give the array of formulas which represents all the 
   * type declarations that were used.
   * @param sorts the types to declare
   * @return an array of type declarations to print
   */
  public static STerm [] generateTypes(final Sort [] sorts) {
    final STerm [] res = new STerm[sorts.length]; 
    for (int i = 0; i < sorts.length; i++) {
      res[i] = generateType(sorts[i]);
    }
    return res;
  }

  /**
   * Translate the given sort to a fully valid formula.
   * @param s the sort to translate
   * @return a term representing the type
   */
  public static STerm generateType(final Sort s) {
    lf.dumpBuilder = lf.builder;
    final STerm res = lf.builder.buildSort(s);
    lf.dumpBuilder = null;
    return res;
  }


  /**
   * Every use of this function should be replaced by a 'proper'
   * library call.
   * @deprecated to be used for convenience only
   * @return returns the current lifter
   */
  public static Lifter getCurrentLifter() {
    return lf;
  }

  /**
   * Tells whether or not we are manipulating the sort Any.
   * @param s the Sort to check
   * @return true if the sort is Any
   */
  public static boolean isAny(final Sort s) {
    return s.equals(sortAny);
  }
}
