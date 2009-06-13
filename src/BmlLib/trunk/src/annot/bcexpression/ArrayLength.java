package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class represents ARRAYLENGTH constant. Eg. expression:
 * array.length
 * should have AST like:
 * FieldAccess(LocalVariable("array"), ARRAYLENGTH())
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ArrayLength extends BCExpression {

  /**
   * A standard constructor.
   */
  public ArrayLength() {
    super(Code.ARRAYLENGTH);
  }

  @Override
  protected JavaType checkType1() {
    return JavaBasicType.JavaInt;
  }

  @Override
  public JavaType getType1() {
    return JavaBasicType.JavaInt;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return "\\length";
  }

  @Override
  public String toString() {
    return "array length";
  }

}
