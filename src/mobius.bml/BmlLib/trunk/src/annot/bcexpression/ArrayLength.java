package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents \length(.) expression. Eg. the equivalent of
 * array.length.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class ArrayLength extends BCExpression {

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - input stream to load from.
   * @param root - type of expression (last byte read from
   *     <code>ar</code>).
   * @throws ReadAttributeException - if root + remaining
   *     stream in <code>ar</code> doesn't represent
   *     correct <code>\length</code> expression.
   */
  public ArrayLength(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor.
   *
   * @param subExpr - it's subexpression.
   */
  public ArrayLength(final BCExpression subExpr) {
    super(Code.ARRAYLENGTH, subExpr);
  }

  /**
   * This method returns the type of this expression provided that all
   * the subexpressions have correct types. In this case, this is
   * "int" ({@link JavaBasicType#JAVA_INT_TYPE}).
   *
   * @return "int" ({@link JavaBasicType#JAVA_INT_TYPE})
   */
  protected JavaType checkType1() {
    return JavaBasicType.JAVA_INT_TYPE;
  }

  /**
   * This method returns the type of this expression. In this case, this is
   * "int" ({@link JavaBasicType#JAVA_INT_TYPE}).
   *
   * @return "int" ({@link JavaBasicType#JAVA_INT_TYPE})
   */
  public JavaType getType1() {
    return JavaBasicType.JAVA_INT_TYPE;
  }

  /**
   * Returns the string representation of the expression which is
   * contained in {@link DisplayStyle#LENGTH_KWD}.
   *
   * @param conf - see {@link BMLConfig}.
   * @return {@link DisplayStyle#LENGTH_KWD}
   */
  protected String printCode1(final BMLConfig conf) {
    return DisplayStyle.LENGTH_KWD + "(" + getSubExpr(0).printCode1(conf) + ")";
  }

  /**
   * @return simple String representation of this
   *     expression, for debugging only.
   */
  public String toString() {
    return DisplayStyle.LENGTH_KWD + "(...)";
  }

  /**
   * Reads the subexpression from an AttributeReader (except
   * connector, that has been already read and set).
   *
   * @param ar - stream to load from,
   * @param root - connentor.
   * @throws ReadAttributeException - if connector + stream
   *     in <code>ar</code> doesn't represent any
   *     expression from calling subclass.
   */
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(1);
    setSubExpr(0, ar.readExpression());
  }
}
