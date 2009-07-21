package annot.bcexpression;

import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents an <code>OLD</code> expression.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class OLD extends BCExpression {

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
   * @param subExpr - it's subexpression.
   */
  public OLD(final BCExpression subExpr) {
    super(Code.OLD, subExpr);
  }

  @Override
  protected JavaType checkType1() {
    return getSubExpr(0).checkType1();
  }

  @Override
  public JavaType getType1() {
    return getSubExpr(0).getType();
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return DisplayStyle.OLD_KWD + "(" + getSubExpr(0).printCode(conf) + ")";
  }

  /**
   * Reads the subexpression from an AttributeReader (except
   * connector, that has been already read and set).
   *
   * @param ar - stream to load from,
   * @param root - connentor.
   * @throws ReadAttributeException - if connector + stream
   *     in <code>ar</code> doesn't represent any
   *     expression from calling subclass.
   */
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(1);
    setSubExpr(0, ar.readExpression());
  }

  @Override
  public String toString() {
    return DisplayStyle.OLD_KWD + "(...)";
  }

}
