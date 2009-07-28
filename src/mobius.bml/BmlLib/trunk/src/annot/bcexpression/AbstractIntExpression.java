package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;

/**
 * This class represents expressions that returns an integer
 * value.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class AbstractIntExpression extends BCExpression {

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - stream to load from,
   * @param root - expression type (connector).
   * @throws ReadAttributeException - if connector + stream
   *     in <code>ar</code> doesn't represent any
   *     expression from constructing subclass.
   * @see BCExpression#BCExpression(AttributeReader, int)
   */
  protected AbstractIntExpression(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * Another constructor for 0Arg expressions.
   *
   * @param connector - type of expression
   *     (from annot.io.Code interface).
   */
  protected AbstractIntExpression(final int connector) {
    super(connector);
  }

  /**
   * A Constructor for unary expressions.
   *
   * @param connector - type of expression
   *     (from annot.io.Code interface),
   * @param subExpr - subexpression.
   */
  protected AbstractIntExpression(final int connector,
                                  final BCExpression subExpr) {
    super(connector, subExpr);
  }

  /**
   * A constructor for binary expressions.
   *
   * @param connector - type of expression
   *     (from annot.io.Code interface),
   * @param left - left subexpression,
   * @param right - right subexrpession.
   */
  protected AbstractIntExpression(final int connector, final BCExpression left,
                                  final BCExpression right) {
    super(connector, left, right);
  }

  @Override
  public JavaType getType1() {
    return JavaBasicType.JAVA_INT_TYPE;
  }

}
