package annot.bcexpression.javatype;

import org.apache.bcel.classfile.ClassFormatException;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.Type;

import annot.bcclass.MLog;
import annot.bcclass.MessageLog;
import annot.bcexpression.BCExpression;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.DisplayStyle;

/**
 * This class represents return type of an expression.
 * The constructor is protected, so use static factories
 * {@link #getJavaType(String)}
 * or {@link #getJavaBasicType(String)} instead.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class JavaType extends BCExpression {

  // type comparation results:

  /**
   * Given type is a subtype of this type.
   */
  public static final int IS_SUBTYPE = 1;

  /**
   * This type is a subtype of given type.
   */
  public static final int IS_SUPERTYPE = 2;

  /**
   * types are equal.
   */
  public static final int TYPES_EQUAL = 3;

  /**
   * Type are totally diffrent (no type is a subtype
   * of the other).
   */
  public static final int TYPES_UNRELATED = 0;

  /**
   * A standard constructor for subclasses.
   */
  protected JavaType() {
    super(Code.JAVA_TYPE);
  }

  @Deprecated
  public static JavaType convert(final Type t) {
    if (t == Type.BOOLEAN) {
      return JavaBasicType.JavaBool;
    }
    if (t == Type.BYTE || t == Type.SHORT || t == Type.INT || t == Type.LONG) {
      return JavaBasicType.JavaInt;
    }
    if (t instanceof ArrayType) {
      return new JavaArrayType(t.getSignature());
    }
    return JavaReferenceType.ANY; //XXX
  }

  /**
   * Gives proper instance of JavaBasicType.
   *
   * @param name - type name, as in variable declaration.
   * @return - instance of JavaType representing type
   *     of given <code>name</code>.
   * @throws ReadAttributeException - if <code>name</code>
   *     parameter is invalid.
   */
  public static JavaBasicType getJavaBasicType(final String name)
    throws ReadAttributeException {
    if (DisplayStyle.JT_INT.equals(name)) {
      return JavaBasicType.JavaInt;
    }
    if (DisplayStyle.JT_BOOLEAN.equals(name)) {
      return JavaBasicType.JavaBool;
    }
    throw new ReadAttributeException("Unknown java type");
  }

  /**
   * Gives proper instance of JavaType.
   *
   * @param name - type name.
   * @return - instance of JavaType representing type
   *     of given <code>name</code>.
   */
  public static JavaType getJavaType(final String name) {
    if (DisplayStyle.JT_INT.equals(name) || "I".equals(name)) {
      return JavaBasicType.JavaInt;
    }
    if (DisplayStyle.JT_BOOLEAN.equals(name) || "B".equals(name)) {
      return JavaBasicType.JavaBool;
    }
    try {
      if (Type.getType(name) instanceof ArrayType) {
        return new JavaArrayType(name);
      }
      return new JavaReferenceType(name);
    } catch (final ClassFormatException cfe) {
      MLog.putMsg(MessageLog.LEVEL_PWARNING, "invalid type name");
      //XXX shouldn't it return null?
      return new JavaReferenceType(name);
    }
  }

  /**
   * @return type of JavaType, that is,
   *     {@link JavaBasicType#JavaType}.
   */
  @Override
  protected JavaType checkType1() {
    return JavaBasicType.JavaType;
  }

  /**
   * Compares this type with given type.<br>
   * //TODO checking for subtypes currently unsupported!
   *
   * @param type - type to compare to.
   * @return <b>{@link #TYPES_UNRELATED}</b> - if neither
   *     this type is a subtype of given one, nor given
   *     type is a subtype of this type,<br>
   *     <b>{@link #IS_SUBTYPE}</b> - if given type
   *     is a subtype of this type,<br>
   *     <b>{@link #IS_SUPERTYPE}</b> - if this type
   *     is a subtype of given type,<br>
   *     <b>{@link #TYPES_EQUAL}</b> - if this type
   *     is equal to given type.
   */
  public abstract int compareTypes(JavaType type);

  /**
   * @return type of JavaType, that is,
   *     {@link JavaBasicType#JavaType}.
   */
  @Override
  public JavaType getType1() {
    return JavaBasicType.JavaType;
  }

}
