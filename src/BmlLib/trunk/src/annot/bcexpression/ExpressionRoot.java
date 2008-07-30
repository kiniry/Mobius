package annot.bcexpression;

import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents a root of an expression.
 * Each attribute should have direct references ONLY to
 * expressions of this type, eg:<br>
 * <b>wrong:</b><br>
 *     Assert.formula = Predicate2Ar(Code.LESS, expr1, expr2);
 * <br><b>correct:</b><br>
 *     Assert.formula = ExpressionRoot(Predicate2Ar(
 *       Code.LESS, expr1, expr2));
 * @param  <T>  - expected type of it's (only) subexpression;
 *     eg. in Assert, use {@link AbstractFormula} as the
 *     assert expression is always a formula.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01

 */
public class ExpressionRoot < T extends BCExpression >  extends BCExpression {

  /**
   * Parent attribute of this expression.
   */
  private final Object attribute;

  /**
   * A standard constructor.
   *
   * @param parent - use <b>this</b> as this parameter value,
   * @param subExpression - the expression this class
   *     should represent.
   */
  public ExpressionRoot(final Object parent, final T subExpression) {
    super(Code.EXPRESSION_ROOT);
    this.attribute = parent;
    this.setSubExprCount(1);
    this.setSubExpr(0, subExpression);
  }

  @Override
  protected JavaType checkType1() {
    return getSubExpr(0).checkType();
  }

  /**
   * @return a parent Object (it's creator, usually
   *     an attribute).
   */
  public Object getAttribute() {
    return this.attribute;
  }

  @SuppressWarnings("unchecked")
  public T getExpression() {
    return (T) getSubExpr(0);
  }

  @Override
  protected int getPriority() {
    return Priorities.MAX_PRI;
  }

  @Override
  public JavaType getType1() {
    return getSubExpr(0).getType();
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printCode(conf);
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    getSubExpr(0).read(ar, root);
  }

  /**
   * Set it's (only) subexpression.
   *
   * @param expr - new subexpression value.
   */
  public void setExpression(final T expr) {
    setSubExpr(0, expr);
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
