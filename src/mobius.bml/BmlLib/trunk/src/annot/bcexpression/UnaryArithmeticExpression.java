package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents unary minus.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class UnaryArithmeticExpression extends UnaryExpression {

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
   * @param connector - type of expression
   * @param subExpr - subexpression.
   */
  public UnaryArithmeticExpression(final int connector,
                                   final BCExpression subExpr) {
    super(connector, subExpr);
  }

  @Override
  protected JavaType checkType1() {
    if (getSubExpr(0).getType() != JavaBasicType.JAVA_INT_TYPE) {
      return null;
    }
    return JavaBasicType.JAVA_INT_TYPE;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return printRoot() + getSubExpr(0).printCode(conf);
  }

  @Override
  public String toString() {
    return printRoot() + getSubExpr(0).toString();
  }

  @Override
  public JavaType getType1() {
    return JavaBasicType.JAVA_INT_TYPE;
  }

  /**
   * @return string representation of expression's root
   */
  private String printRoot() {
    switch (getConnector()) {
      case Code.BITWISENOT:
        return " ~ ";
      case Code.NEG:
        return " -";
      default:
        throw new RuntimeException("unknown unary opcode: " +
                                   getConnector());
    }
  }

}
