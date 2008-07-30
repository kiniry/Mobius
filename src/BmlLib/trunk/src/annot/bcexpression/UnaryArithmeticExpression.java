package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents unary minus.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class UnaryArithmeticExpression extends ArithmeticExpression {

  /**
   * A constructor from AttributeReader, used for loading
   * from file (from BCEL's unknown Attribute).
   *
   * @param ar - input stream to load from,
   * @param root - type o expression (last read byte from
   *     <code>ar</code>.
   * @throws ReadAttributeException - if stream
   *     in <code>ar</code> doesn't represent any correct
   *     expression.
   * @see BCExpression#BCExpression(AttributeReader, int)
   */
  public UnaryArithmeticExpression(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor.
   *
   * @param connector - type of exrpession, should be
   *     {@link Code#NEG},
   * @param subExpr - subexpression.
   */
  public UnaryArithmeticExpression(final int connector,
                                   final BCExpression subExpr) {
    super(connector, subExpr);
  }

  @Override
  protected JavaType checkType1() {
    if (getSubExpr(0).getType() != JavaBasicType.JavaInt) {
      return null;
    }
    return JavaBasicType.JavaInt;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return printRoot() + getSubExpr(0).printCode(conf);
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(1);
    final BCExpression sub = ar.readExpression();
    setSubExpr(0, sub);
  }

  @Override
  public String toString() {
    return printRoot() + getSubExpr(0).toString();
  }

}
