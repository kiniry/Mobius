package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * Represents artihmetic expressions (int x int -- >  int),
 * including shifts and bit operations.
 * Unary arithmetic operation (unary minus) has been moved
 * to the {@link UnaryArithmeticExpression}.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ArithmeticExpression extends AbstractIntExpression {
  //XXX should bitwise and shifts expressions be separated from arithmetic
  //    expressions?
  //what is the important differecne between those expression types?

  /**
   * A constructor from AttributeReader, used for loading
   * from file (from BCEL's unknown Attribute).
   *
   * @param ar - input stream to load from,
   * @param root - type o expression (last read byte from
   *     <code>ar</code>.
   * @throws ReadAttributeException - if stream
   *     in <code>ar</code> doesn't represent a correct
   *     artimethic expression.
   * @see BCExpression#BCExpression(AttributeReader, int)
   */
  public ArithmeticExpression(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A constructor for unary minus only.
   */
  protected ArithmeticExpression(final int connector,
                                 final BCExpression subExpr) {
    super(connector, subExpr);
  }

  /**
   * A standard constructor.
   *
   * @param connector - type of expression, from
   *     <code>Code</code> interface,
   * @param left - left subexpression,
   * @param right - right subexpression.
   */
  public ArithmeticExpression(final int connector, final BCExpression left,
                              final BCExpression right) {
    super(connector, left, right);
  }

  @Override
  protected JavaType checkType1() {
    if (getSubExpr(0).getType() != JavaBasicType.JavaInt ||
        getSubExpr(1).getType() != JavaBasicType.JavaInt) {
      return null;
    }
    return JavaBasicType.JavaInt;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printCode(conf) + printRoot() +
      getSubExpr(1).printCode(conf);
  }

  /**
   * @return string representation of expression's connector.
   */
  protected String printRoot() {
    switch (getConnector()) {
      case Code.BITWISENOT:
        return " ~ ";
      case Code.BITWISEAND:
        return " & ";
      case Code.BITWISEOR:
        return " | ";
      case Code.BITWISEXOR:
        return " ^ ";
      case Code.DIV:
        return " / ";
      case Code.MINUS:
        return " - ";
      case Code.MULT:
        return " * ";
      case Code.NEG:
        return " -";
      case Code.PLUS:
        return " + ";
      case Code.REM:
        return " % ";
      case Code.SHL:
        return "  <<  ";
      case Code.SHR:
        return "  >>  ";
      case Code.USHR:
        return "  >>  >  "; //XXX
      default:
        throw new RuntimeException("unknown arithmetic opcode: " +
                                   getConnector());
    }
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(2);
    final BCExpression left = ar.readExpression();
    final BCExpression right = ar.readExpression();
    setSubExpr(0, left);
    setSubExpr(1, right);
  }

  @Override
  public String toString() {
    return "(" + getSubExpr(0).toString() + printRoot() +
      getSubExpr(1).toString() + ")";
  }

}
