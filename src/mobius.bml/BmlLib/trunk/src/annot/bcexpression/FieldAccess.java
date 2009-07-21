package annot.bcexpression;

import annot.bcexpression.javatype.JavaArrayType;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents dot expression (obj.field).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class FieldAccess extends BCExpression {

  /**
   * A constructor from AtributeReader.
   *
   * @param ar - input stream to load from,
   * @param root - connector (last byte read from
   *     <code>ar</code>).
   * @throws ReadAttributeException - if root + remaining
   *     stream in <code>ar</code> doesn't represent
   *     corrent field access expression.
   */
  public FieldAccess(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor.
   *
   * @param connector - type of expression, should be
   *     {@link Code#FIELD_ACCESS},
   * @param left - left subexpression (an object),
   * @param right - right subexpression (<code>left</code>'s
   *     field).
   */
  public FieldAccess(final int connector, final BCExpression left,
                     final BCExpression right) {
    super(connector, left, right);
  }

  @Override
  protected JavaType checkType1() {
    if (getSubExpr(1) instanceof ArrayLength) {
      if (!(getSubExpr(0).getType() instanceof JavaArrayType)) {
        return null;
      }
    } else if (!(getSubExpr(0).getType() instanceof JavaReferenceType)) {
      return null;
    }
    return getSubExpr(1).getType();
  }

  @Override
  public JavaType getType1() {
    return getSubExpr(1).getType();
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printCode(conf) + "." + getSubExpr(1).printCode(conf);
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(2);
    setSubExpr(0, ar.readExpression());
    setSubExpr(1, ar.readExpression());
  }

  @Override
  public String toString() {
    return getSubExpr(0).toString() + "." + getSubExpr(1).toString();
  }

}
