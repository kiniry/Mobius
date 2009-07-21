package mobius.bmlvcgen.vcgen;

import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;

import org.apache.bcel.generic.ObjectType;

import escjava.sortedProver.Lifter.QuantVariable;

/**
 * Contains implementations of some methods
 * from Expression class. The problem with
 * original implementations is that they
 * are dependent on javafe ast elements.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class ExprHelper {
  /** Constructor - not callable. */
  private ExprHelper() {
  }
  
  /**
   * Create a field name.
   * @param cls Class in which the field is declared.
   * @param name Field name.
   * @return Variable.
   */
  public static QuantVariable getFieldVar(
      final ObjectType cls, final String name) {
    return Expression.var(cls.getClassName() + "Signature?" + name + 
                          "FieldSignature", Heap.sortValue);
  }
}
