package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.Priorities;

/**
 * This class represents expressions that says what can
 * be affected by some code, eg. method, loop or block.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class ModifyExpression extends BCExpression {

  /**
   * This says that described code can affect any variable.
   * (or that we have no information about what can
   * be affected by described code).
   */
  public static final ModifiesEverything EVERYTHING_MODIF =
    new ModifiesEverything();

  /**
   * This says that described code won't affect
   * any variables.
   */
  public static final ModifiesNothing NOTHING_MODIF =
    new ModifiesNothing();

  /**
   * A constructor from AttributeReader. It assumes that
   * expression type (connector, from <code>Code</code>
   * interface) has been just loaded from <code>ar</code>.
   *
   * @param ar - AttributeReader to load from.
   * @param root - type of this expression, eg. last byte
   *     read by <code>ar</code>.
   * @throws ReadAttributeException - if remainig data
   *     in input stream (<code>ar</code>) doesn't
   *     represent correct modify expression.
   */
  protected ModifyExpression(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor, for subclasses.
   *
   * @param connector - type of this expression,
   *     as in <code>Code</code> interface.
   */
  protected ModifyExpression(final int connector) {
    super(connector);
  }

  /**
   * Another constructor, for unary subclasses.
   *
   * @param connector - type of this expression,
   *     as in <code>Code</code> interface,
   * @param expr - subExpression.
   */
  protected ModifyExpression(final int connector, final BCExpression expr) {
    super(connector, expr);
  }

  /**
   * Another constructor, for binary subclasses.
   *
   * @param connector - type of this expression,
   *     as in <code>Code</code> interface,
   * @param left - left subexpression,
   * @param right - right subexpression.
   */
  protected ModifyExpression(final int connector, final ModifyExpression left,
                             final BCExpression right) {
    super(connector, left, right);
  }

  /**
   * Noone should need JavaType of Modify Expression.
   * I will return here sth if I will need JavaType
   * of modify expression.
   *
   * @return always {@link RuntimeException} is thrown
   */
  protected JavaType checkType1() {
    throw new RuntimeException("What type should it return?");
  }

  /**
   * Modify expression is assumed to be displayed at the
   * root of the BCExpression only, so it has the highest
   * priority.
   *
   * @return maximal priority of expressions (from {@link Priorities}).
   */
  @Override
  protected int getPriority() {
    return Priorities.MAX_PRI;
  }

  /**
   * Noone should need JavaType of Modify Expression.
   * I will return here sth if I will need JavaType
   * of modify expression.
   *
   * @return always {@link RuntimeException} is thrown
   */
  @Override
  public JavaType getType1() {
    throw new RuntimeException("What type should it return?");
  }

}
