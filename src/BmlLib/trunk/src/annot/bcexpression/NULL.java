package annot.bcexpression;

import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class represents <code>null</code> value.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class NULL extends BCExpression {

  /**
   * A standard constructor.
   */
  public NULL() {
    super(Code.NULL);
  }

  /**
   * This method returns the type of this expression provided that all
   * the subexpressions have correct types. In this case, this is
   * {@link JavaReferenceType#ANY}.
   *
   * @return the type of the expression ({@link JavaReferenceType#ANY})
   */
  protected JavaType checkType1() {
    return JavaReferenceType.ANY;
  }

  /**
   * This method returns the type of this expression. In this case, this is
   * {@link JavaReferenceType#ANY}.
   *
   * @return the type of the expression ({@link JavaReferenceType#ANY})
   */
  public JavaType getType1() {
    return JavaReferenceType.ANY;
  }

  /**
   * Returns the string representation of the expression i.e. "null" String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return "null" String
   */
  protected String printCode1(final BMLConfig conf) {
    return "null";
  }

  /**
   * @return Simple String representation of this
   *     expression, for debugging only.
   */
  public String toString() {
    return "null";
  }

}
