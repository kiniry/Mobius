package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.ReadAttributeException;

/**
 * This class is a generic superclass for the unary expressions
 * (e.g. \old(), \type() etc.).
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public abstract class UnaryExpression extends BCExpression {

  /**
   * A standard constructor for the given operation name and the subexpression.
   *
   * @param connector the main operand of the expression
   * @param subExpr - subexpression.
   */
  protected UnaryExpression(final int connector, final BCExpression subExpr) {
    super(connector, subExpr);
  }

  /**
   * A constructor which loads from the given AttributeReader the content
   * of the expression.
   *
   * @param ar the reader to load from,
   * @param root - type of expression (last read byte from
   *     <code>ar</code>.
   * @throws ReadAttributeException - if stream
   *     in <code>ar</code> doesn't represent any correct
   *     expression.
   * @see BCExpression#BCExpression(AttributeReader, int)
   */
  protected UnaryExpression(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * Reads the subexpression from an AttributeReader (except
   * the unary expression identifier, that has been already read and set).
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
    final BCExpression sub = ar.readExpression();
    setSubExpr(0, sub);
  }


}
