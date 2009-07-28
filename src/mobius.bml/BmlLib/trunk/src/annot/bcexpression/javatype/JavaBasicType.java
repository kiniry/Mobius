package annot.bcexpression.javatype;

import annot.io.AttributeWriter;
import annot.io.Code;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents basic return type of an expression.
 * The constructor is private, so use
 * {@link JavaType#getJavaType(String)} instead.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public final class JavaBasicType extends JavaType {

  /**
   * The boolean type.
   */
  public static final JavaBasicType JAVA_BOOLEAN_TYPE =
    new JavaBasicType(DisplayStyle.JT_BOOLEAN);

  /**
   * The int type.
   */
  public static final JavaBasicType JAVA_INT_TYPE =
    new JavaBasicType(DisplayStyle.JT_INT);

  /**
   * Type of JavaClass subclasses only.
   */
  public static final JavaBasicType JavaType = new JavaBasicType(null);

  /**
   * The type of modifies expressions.
   */
  public static final JavaBasicType MODIFIES_TYPE =
    new JavaBasicType(null);

  /**
   * String representation of JavaType.
   */
  private final String name;

  /**
   * A private constructor.
   *
   * @param aname - string representation of JavaType.
   */
  private JavaBasicType(final String aname) {
    this.name = aname;
  }

  @Override
  public int compareTypes(final JavaType type) {
    if (type == this) {
      return TYPES_EQUAL;
    }
    return TYPES_UNRELATED;
  }

  /**
   * Displays JavaType to a String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of JavaType.
   * @see BCExpression#printCode1(BMLConfig)
   */
  @Override
  public String printCode1(final BMLConfig conf) {
    return this.name;
  }

  /**
   * @return Simple String representation of this
   *     JavaType, for debugging only.
   */
  @Override
  public String toString() {
    return this.name;
  }

  /**
   * Writes this expression to AttributeWirter.
   *
   * @param aw - stream to save to.
   */
  @Override
  public void write(final AttributeWriter aw) {
    aw.writeByte(Code.JAVA_TYPE);
    final int cpIndex = aw.findConstant(this.name);
    aw.writeShort(cpIndex);
  }

}
