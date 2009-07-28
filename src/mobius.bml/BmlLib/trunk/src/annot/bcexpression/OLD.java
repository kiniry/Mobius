package annot.bcexpression;

import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents an <code>\old</code> expression.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class OLD extends UnaryExpression {

  /**
   * A constructor which reads in the content of the
   * expression from the given {@link AttributeReader}.
   *
   * @param ar - input stream to load from.
   * @param root - type of expression (last byte read from
   *     <code>ar</code>).
   * @throws ReadAttributeException - if root + remaining
   *     stream in <code>ar</code> doesn't represent
   *     correct <code>OLD</code> expression.
   */
  public OLD(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor with subexpression.
   *
   * @param subExpr the argument of \old.
   */
  public OLD(final BCExpression subExpr) {
    super(Code.OLD, subExpr);
  }

  /**
   * This method returns the type of this expression provided that all
   * the subexpressions have correct types. In this case, this is
   * the type of the expression in the argument.
   *
   * @return the type of the old expression
   */
  protected JavaType checkType1() {
    return getSubExpr(0).checkType1();
  }

  /**
   * This method returns the type of this expression. In this case, this is
   * the type of its argument.
   *
   * @return the type of the old expression
   */
  public JavaType getType1() {
    return getSubExpr(0).getType();
  }

  /**
   * Returns the string representation of the expression which is
   * the old keyword followed by the subexpression in ().
   *
   * @param conf - see {@link BMLConfig}.
   * @return {@link DisplayStyle#RESULT_KWD}
   */
  protected String printCode1(final BMLConfig conf) {
    return DisplayStyle.OLD_KWD + "(" + getSubExpr(0).printCode(conf) + ")";
  }

  /**
   * @return simple String representation of this
   *     expression, for debugging only.
   */
  public String toString() {
    return DisplayStyle.OLD_KWD + "(...)";
  }

}
