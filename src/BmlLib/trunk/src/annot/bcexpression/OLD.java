package annot.bcexpression;

import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents an <code>OLD</code> expression.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class OLD extends OldExpression {

  /**
   * A constructor from AttributeReader.
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
   * A standard constructor.
   *
   * @param connector - type of this expression, should
   *     be {@link Code#OLD},
   * @param subExpr - it's subexpression.
   */
  public OLD(final int connector, final BCExpression subExpr) {
    super(makeOld(connector), subExpr);
  }

  @Override
  protected JavaType checkType2() {
    return getSubExpr(0).getType();
  }

  @Override
  public JavaType getType1() {
    return getSubExpr(0).getType();
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return "\\old(" + getSubExpr(0).printCode(conf) + ")";
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(1);
    setSubExpr(0, ar.readExpression());
  }

  @Override
  public String toString() {
    return "\\old(" + getSubExpr(0).toString() + ")";
  }

}
