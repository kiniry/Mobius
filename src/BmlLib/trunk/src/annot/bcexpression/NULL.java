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

  @Override
  protected JavaType checkType1() {
    return JavaReferenceType.ANY;
  }

  @Override
  public JavaType getType1() {
    return JavaReferenceType.ANY;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return "null";
  }

  @Override
  public String toString() {
    return "null";
  }

}
