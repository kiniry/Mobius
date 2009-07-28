package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents a conditionalExpression (?:).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ConditionalExpression extends AbstractIntExpression {

  /**
   * A constructor from AttributeReader, used for loading
   * from file (from BCEL's unknown Attribute).
   *
   * @param ar - input stream to load from,
   * @param root - type o expression (last read byte from
   *     <code>ar</code>.
   * @throws ReadAttributeException - if stream
   *     in <code>ar</code> doesn't represent a correct
   *     conditional expression.
   * @see BCExpression#BCExpression(AttributeReader, int)
   */
  public ConditionalExpression(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor.<br>
   * <code>condition</code> ? <code>iftrue</code> : <br>
   * <code>iffalse</code>
   *
   * @param condition - a boolean expression,
   * @param ifTrue - integer expression; value of this
   *     expression if <code>condition</code> evaluates
   *     to true,
   * @param ifFalse - integer expression; value of this
   *     expression if <code>condition</code> evaluates
   *     to false.
   */
  public ConditionalExpression(final BCExpression condition,
                               final BCExpression ifTrue,
                               final BCExpression ifFalse) {
    super(Code.COND_EXPR);
    setSubExprCount(3);
    setSubExpr(0, condition);
    setSubExpr(1, ifTrue);
    setSubExpr(2, ifFalse);
  }

  @Override
  protected JavaType checkType1() {
    if (getSubExpr(0).getType() != JavaBasicType.JAVA_BOOLEAN_TYPE ||
        getSubExpr(1).getType() != JavaBasicType.JAVA_INT_TYPE ||
        getSubExpr(2).getType() != JavaBasicType.JAVA_INT_TYPE) {
      return null;
    }
    return JavaBasicType.JAVA_INT_TYPE;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printCode(conf) + " ? " +
      getSubExpr(1).printCode(conf) + " : " +
      getSubExpr(2).printCode(conf);
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    final BCExpression cond = ar.readExpression();
    final BCExpression ifTrue = ar.readExpression();
    final BCExpression ifFalse = ar.readExpression();
    setSubExprCount(3);
    setSubExpr(0, cond);
    setSubExpr(1, ifTrue);
    setSubExpr(2, ifFalse);
  }

  @Override
  public String toString() {
    return getSubExpr(0).toString() + " ? " + getSubExpr(1).toString() + " : " +
      getSubExpr(2).toString();
  }

}
