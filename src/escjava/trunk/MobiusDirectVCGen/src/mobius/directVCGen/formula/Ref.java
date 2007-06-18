package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * The library part to handle things that have to do with reference.
 * @author J. Charles (julien.charles@inria.fr), H. Lehner
 */
public final class Ref {  
  /** the sort that represents references. */
  public static Sort sort = Formula.lf.sortRef;

  /** the variable made to represent this. */
  public static QuantVariableRef varThis = Expression.rvar(Expression.var("this", Ref.sort));

  /**
   * @deprecated
   */
  private Ref() { 
  }
  
  /**
   * The symbol that represents null.
   * @return the term that represents null
   */
  public static Term Null() {
    return Formula.lf.mkNullLiteral();
  }

  /**
   * Build a string reference out of the given string.
   * @param str the string to convert to the 
   * representation of the string object.
   * @return a term of type ref representing a string object
   */
  public static Term strValue(final String str) {
    return Formula.lf.symbolRef(str);
  }


}
