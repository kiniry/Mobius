package annot.bcexpression;

import annot.bcclass.BCMethod;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents <code>\result</code> expression
 * (return value of a method).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class RESULT extends BCExpression {

  /**
   * Method whose return value it represents.
   */
  private final BCMethod method;

  /**
   * Return type of method <code>m</code>.
   */
  private final JavaType type;

  /**
   * A standard constructor.
   *
   * @param m - initializing method.
   */
  public RESULT(final BCMethod m) {
    super(Code.RESULT);
    this.method = m;
    this.type = JavaType.getJavaType(m.getBcelMethod().getReturnType()
        .getSignature());
  }

  @Override
  protected JavaType checkType1() {
    return this.type;
  }

  /**
   * @return method whose return value it represents.
   */
  public BCMethod getMethod() {
    return this.method;
  }

  @Override
  public JavaType getType1() {
    return this.type;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return DisplayStyle._result;
  }

  @Override
  public String toString() {
    return DisplayStyle._result;
  }

}
