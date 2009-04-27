package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.Priorities;

/**
 * Describes modification of array's elements (which elements
 * can be modified).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class SpecArray extends BCExpression {

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - input stream to load from,
   * @param root - type of this expression.
   * @throws ReadAttributeException - if root + stream
   *     in <code>ar</code> doesn't represent correct
   *     array modification specification.
   */
  public SpecArray(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor for 0-args array specifications.
   *
   * @param connector - type of expression.
   */
  public SpecArray(final int connector) {
    super(connector);
  }

  /**
   * A standard constructor for unary array specifications.
   *
   * @param connector - type of expression,
   * @param expr - it's subexpression.
   */
  public SpecArray(final int connector, final BCExpression expr) {
    super(connector, expr);
  }

  /**
   * A standard constructor for binary array specifications.
   *
   * @param connector - type of expression,
   * @param left - left subexpression,
   * @param right - right subexpression.
   */
  public SpecArray(final int connector, final BCExpression left,
                   final BCExpression right) {
    super(connector, left, right);
  }

  /**
   * Noone should need JavaType of SpecArray.
   * I will return here sth if I will need JavaType
   * of this expression.
   *
   * @return always {@link RuntimeException} is thrown
   */
  protected JavaType checkType1() {
    throw new RuntimeException("What type should it return?");
  }

  /**
   * @return maximal priority of expressions (from {@link Priorities}).
   */
  protected int getPriority() {
    return Priorities.MAX_PRI;
  }

  /**
   * Nobody should need JavaType of SpecArray.
   * I will return here sth if I will need JavaType
   * of this expression.
   *
   * @return always {@link RuntimeException} is thrown
   */
  public JavaType getType1() {
    throw new RuntimeException("What type should it return?");
  }

}
