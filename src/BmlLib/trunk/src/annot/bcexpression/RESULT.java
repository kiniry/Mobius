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
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
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

  /**
   * This method returns the type of this expression provided that all
   * the subexpressions have correct types. In this case, this is
   * the type of the method to which the result is assigned.
   *
   * @return the type of the method with this result
   */
  protected JavaType checkType1() {
    return this.type;
  }

  /**
   * @return method whose return value it represents.
   */
  public BCMethod getMethod() {
    return this.method;
  }

  /**
   * This method returns the type of this expression. In this case, this is
   * the type of the method to which the result is assigned.
   *
   * @return the type of the method with this result
   */
  public JavaType getType1() {
    return this.type;
  }

  /**
   * Returns the string representation of the expression which is
   * contained in {@link DisplayStyle#RESULT_KWD}.
   *
   * @param conf - see {@link BMLConfig}.
   * @return {@link DisplayStyle#RESULT_KWD}
   */
  protected String printCode1(final BMLConfig conf) {
    return DisplayStyle.RESULT_KWD;
  }

  /**
   * @return simple String representation of this
   *     expression, for debugging only.
   */
  public String toString() {
    return DisplayStyle.RESULT_KWD;
  }

}
