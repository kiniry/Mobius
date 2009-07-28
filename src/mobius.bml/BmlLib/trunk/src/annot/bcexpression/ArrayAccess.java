package annot.bcexpression;

import annot.bcexpression.javatype.JavaArrayType;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents array element reference.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ArrayAccess extends BCExpression {

  public ArrayAccess(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor,
   * for <code>array</code>[<code>index</code>] expression.
   *
   * @param array - an expression representing an array
   *     variable.
   * @param index - an expression representing index in
   *     <code>array</code>.
   */
  public ArrayAccess(final BCExpression array, final BCExpression index) {
    super(Code.ARRAY_ACCESS, array, index);
  }

  @Override
  protected JavaType checkType1() {
    if (getSubExpr(1).getType() != JavaBasicType.JAVA_INT_TYPE) {
      return null;
    }
    final JavaType t = getSubExpr(0).getType();
    if (!(t instanceof JavaArrayType)) {
      return null;
    }
    return ((JavaArrayType) t).getSingleType();
  }

  @Override
  public JavaType getType1() {
    return ((JavaArrayType) getSubExpr(0).getType()).getSingleType();
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printRawCode(conf) + "[" +
      getSubExpr(1).printRawCode(conf) + "]";
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(2);
    setSubExpr(0, ar.readExpression());
    setSubExpr(1, ar.readExpression());
  }

  @Override
  public String toString() {
    return getSubExpr(0).toString() + "[" + getSubExpr(1).toString() + "]";
  }

}
