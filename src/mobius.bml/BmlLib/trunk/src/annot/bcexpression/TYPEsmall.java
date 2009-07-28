package annot.bcexpression;

import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents an <code>\type()</code> expression.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class TYPEsmall extends UnaryExpression {

  /**
   * A constructor which reads in the content of the
   * expression from the given {@link AttributeReader}.
   *
   * @param ar - input stream to load from.
   * @param root - type of expression (last byte read from
   *     <code>ar</code>).
   * @throws ReadAttributeException - if root + remaining
   *     stream in <code>ar</code> doesn't represent
   *     correct <code>\type</code> expression.
   */
  public TYPEsmall(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor with subexpression.
   *
   * @param subExpr the argument of \type.
   */
  public TYPEsmall(final BCExpression subExpr) {
    super(Code.TYPE_SMALL, subExpr);
  }

  /**
   *
   * This method returns the type of this expression provided that all
   * the subexpressions have correct types. In this case, the
   * representation of \TYPE is returned, provided that the subexpression
   * can be correctly typed. Otherwise,  <code>null</code> is returned.
   *
   * @return \TYPE (or <code>null</code> in case the subexpression cannot be
   *   typed)
   */
  protected JavaType checkType1() {
    if (getSubExpr(0).checkType1() == null) return null;
    return JavaType.getJavaType(DisplayStyle.TYPE_KWD);
  }

  /**
   * This method returns the type of this expression. In this case, this is
   * the representation of \TYPE, as JML Reference Manual, section 11.4.18 \type
   * says: <i>An expression of the form \type(T), where T is a type name, has
   * the type \TYPE</i>.
   *
   * @return the type \TYPE
   */
  public JavaType getType1() {
    return JavaType.getJavaType(DisplayStyle.TYPE_KWD);
  }

  /**
   * @return simple String representation of this
   *     expression, for debugging only.
   */
  public String toString() {
    return DisplayStyle.TYPE_SMALL_KWD + "(...)";
  }

  /**
   * Returns the string representation of the expression which is
   * the \type keyword followed by the subexpression in ().
   *
   * @param conf - see {@link BMLConfig}.
   * @return the String with the current expression
   */
  protected String printCode1(final BMLConfig conf) {
    return DisplayStyle.TYPE_SMALL_KWD +
      "(" + getSubExpr(0).printCode(conf) + ")";
  }

}
