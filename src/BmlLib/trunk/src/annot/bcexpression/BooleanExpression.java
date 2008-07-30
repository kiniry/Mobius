package annot.bcexpression;

import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeWriter;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This ugly class converts an expression
 * to {@link AbstractFormula}. It should be used when
 * we have an boolean expression (that is, it's checkType()
 * method evaluates to {@link JavaBasicType#JavaBool}),
 * but it is'n an {@link AbstractFormula}'s subclass.
 * It can happen, for example, in attribute: "\assert b",
 * where b is a boolean local variable. Assert's formula
 * should have boolean return type, but LocalVariable is
 * a direct {@link BCExpression} subclass (we would need
 * as many classes as there is many types for local variable
 * to ensure it's static type control). In this case, AST
 * should look like:
 * assert(BooleanExpression(LocalVariable("b")))
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class BooleanExpression extends AbstractFormula {

  /**
   * A standard constructor.
   *
   * @param subExpr - expression it should represent.
   *     It should have a boolean return type, but
   *     it shouldn't be an AbstractFormula.
   */
  public BooleanExpression(final BCExpression subExpr) {
    super(-1, subExpr);
  }

  @Override
  protected JavaType checkType1() {
    final JavaType type = getSubExpr(0).getType();
    if (type != JavaBasicType.JavaBool) {
      return null;
    }
    return JavaBasicType.JavaBool;
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
