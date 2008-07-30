package annot.bcexpression;

import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class represents a shared object (bound or local
 * variable) reference.<br>
 * One instance per one occurence in expression.<br>
 * It's <code>sharedExpr</code> attribute can be the same (==)
 * in diffrent <code>SingleOccurence</code> expressions, eg.
 * Each reference to the same variable is diffrent expression,
 * but their's <code>sharedExpr</code> attribute is the same.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class SingleOccurence extends BCExpression {

  /**
   * Shared object (bound or local variable) this expression
   * referes to.
   */
  private final BCExpression sharedExpr;

  /**
   * A standard constructor.
   *
   * @param expr - shared variable this expression
   *     refers to.
   */
  public SingleOccurence(final BCExpression expr) {
    super(Code.SINGLE_OCCURENCE);
    this.sharedExpr = expr;
  }

  @Override
  protected JavaType checkType1() {
    return this.sharedExpr.checkType1();
  }

  /**
   * @return shared object (bound or local variable)
   * this expression referes to.
   */
  public BCExpression getSharedExpr() {
    return this.sharedExpr;
  }

  @Override
  public JavaType getType1() {
    return this.sharedExpr.getType();
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return this.sharedExpr.printCode1(conf);
  }

  @Override
  public String toString() {
    return this.sharedExpr.toString();
  }

  @Override
  public void write(final AttributeWriter aw) {
    this.sharedExpr.write(aw);
  }

}
