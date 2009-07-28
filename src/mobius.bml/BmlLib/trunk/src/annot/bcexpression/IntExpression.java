package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeWriter;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This ugly class converts an expression
 * to {@link AbstractIntExpression}.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 * @see BooleanExpression
 */
public class IntExpression extends AbstractIntExpression {

  /**
   * A standard constructor.
   *
   * @param subExpr - expression it should represent.
   *     It should have a int return type, but
   *     it shouldn't be an AbstractIntExpression.
   */
  public IntExpression(final BCExpression subExpr) {
    super(-1, subExpr);
  }

  @Override
  protected JavaType checkType1() {
    final JavaType type = getSubExpr(0).getType();
    if (type != JavaBasicType.JAVA_INT_TYPE) {
      return null;
    }
    return JavaBasicType.JAVA_INT_TYPE;
  }

  @Override
  protected int getPriority() {
    return Priorities.PRI_TRANSPARENT;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printRawCode(conf);
  }

  @Override
  public String toString() {
    return getSubExpr(0).toString();
  }

  @Override
  public void write(final AttributeWriter aw) {
    getSubExpr(0).write(aw);
  }

}
