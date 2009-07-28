package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents an <code>\nonnullelements()</code> expression.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class NONNULLELEMENTS extends UnaryExpression {

  /**
   * A constructor which reads in the content of the
   * expression from the given {@link AttributeReader}.
   *
   * @param ar - input stream to load from.
   * @param root - type of expression (last byte read from
   *     <code>ar</code>).
   * @throws ReadAttributeException - if root + remaining
   *     stream in <code>ar</code> doesn't represent
   *     correct <code>\nonnullelements</code> expression.
   */
  public NONNULLELEMENTS(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor with subexpression.
   *
   * @param subExpr the argument of \nonnullelements.
   */
  public NONNULLELEMENTS(final BCExpression subExpr) {
    super(Code.NONNULLELEMENTS, subExpr);
  }

  /**
  *
  * This method returns the type of this expression provided that all
  * the subexpressions have correct types. In this case, the
  * representation of boolean type is returned, provided that the subexpression
  * can be correctly typed. Otherwise,  <code>null</code> is returned.
  *
  * @return {@link JavaBasicType#JAVA_BOOLEAN_TYPE}
  *   (or <code>null</code> in case the subexpression cannot be typed)
  */
  protected JavaType checkType1() {
    if (getSubExpr(0).checkType1() == null) return null;
    return getType1();
  }

  /**
   * This method returns the type of this expression. In this case, the
  * representation of boolean type is returned.
   *
   * @return the type {@link JavaBasicType#JAVA_BOOLEAN_TYPE}
   */
  public JavaType getType1() {
    return JavaBasicType.JAVA_BOOLEAN_TYPE;
  }

  /**
   * Returns the string representation of the expression which is
   * the \nonnullelements keyword followed by the subexpression in ().
   *
   * @param conf - see {@link BMLConfig}.
   * @return the String with the current expression
   */
  protected String printCode1(final BMLConfig conf) {
    return DisplayStyle.NONNULLELEMENTS_KWD +
      "(" + getSubExpr(0).printCode(conf) + ")";
  }

  /**
   * @return simple String representation of this
   *     expression, for debugging only.
   */
  public String toString() {
    return DisplayStyle.NONNULLELEMENTS_KWD + "(...)";
  }

}
