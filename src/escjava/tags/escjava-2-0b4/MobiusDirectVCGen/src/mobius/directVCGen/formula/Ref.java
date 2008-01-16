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
  public static final Sort sort = Formula.lf.sortRef;

  /** the variable made to represent this. */
  public static final QuantVariableRef varThis = Expression.rvar(
                                             Expression.var("this", 
                                                            Heap.sortValue));

  /**
   * @deprecated
   */
  private Ref() { 
  }
  
  /**
   * The symbol that represents null.
   * @return the term that represents null
   */
  public static Term nullValue() {
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

  /**
   * Returns the term representing the conversion from a location
   * to a reference.
   * @param var a variable of the type location
   * @return a variables of the type reference
   */
  public static QuantVariableRef fromLoc(final QuantVariableRef var) {
    String name = var.qvar.name;
    
    final Sort s = var.getSort();
    if (name.startsWith("#")) {
      name = name.substring(1);
      name = "#(Ref " + name + ")";
    }
    else {
      name = "(Ref " + name + ")";
    }
    return Expression.rvar(name, s);
  }


}
