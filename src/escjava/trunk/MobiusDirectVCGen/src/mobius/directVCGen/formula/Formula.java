package mobius.directVCGen.formula;

import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.Lifter;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.STerm;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * This is the library class for generic handling of the formulas.
 * It is not used to create terms. The sort attached to it
 * is the sort any... But it should not be used (yes - it is
 * marked as deprecated).
 */
public class Formula {

  /** the current instance of the lifter: used to build the formulas */
  static Lifter lf = new Lifter(new CoqNodeBuilder());

  /** 
   * the sort that represents any sort... should not be used 
   * @deprecated use any other sort from any other library
   */
  public static Sort sort = lf.sortAny;
  /**
   * program is inner to Coq's representation: it is
   * dubious that it should appear in formulas
   * @deprecated use only at the Coq level
   */
  public static QuantVariable program = Expression.var("p");

  /** the sort used to represent a value */
  public static Sort sortValue = lf.sortValue;

  /**
   * Generate the formulas from a given term using the
   * current lifter.
   * @param t The terms to translate
   * @return the formulas ready to be dumped
   */
  public static STerm generateFormulas(Term t) {
    lf.dumpBuilder = lf.builder;
    STerm st = t.dump();
    lf.dumpBuilder = null;
    return st;
  }

  /**
   * Give the array of formulas which represents all the 
   * type declarations that were used.
   * @param sorts the types to declare
   * @return an array of type declarations to print
   */
  public static STerm [] generateTypes(Sort [] sorts) {
    STerm [] res = new STerm[sorts.length]; 
    for(int i = 0; i < sorts.length; i++) {
      res[i] = generateType(sorts[i]);
    }
    return res;
  }

  /**
   * Translate the given sort to a fully valid formula.
   * @param sort the sort to translate
   * @return a term representing the type
   */
  public static STerm generateType(Sort sort) {
    lf.dumpBuilder = lf.builder;
    STerm res = lf.builder.buildSort(sort);
    lf.dumpBuilder = null;
    return res;
  }


  /**
   * Every use of this function should be replaced by a 'proper'
   * library call.
   * @deprecated to be used for convenience only
   */
  public static Lifter getCurrentLifter() {
    return lf;
  }

}
