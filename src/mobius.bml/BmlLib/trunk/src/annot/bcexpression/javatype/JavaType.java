package annot.bcexpression.javatype;

import org.apache.bcel.classfile.ClassFormatException;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.Type;

import annot.bcclass.MLog;
import annot.bcclass.MessageLog;
import annot.bcexpression.BCExpression;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents return type of an expression.
 * The constructor is protected, so use static factories
 * {@link #getJavaType(String)} or {@link #getJavaBasicType(String)} instead.
 * This class represents also the \TYPE type declaration.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class JavaType extends BCExpression {

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
   * The types are equal.
   */
  public static final int TYPES_EQUAL = 3;

  /**
   * Type are totally diffrent (no type is a subtype
   * of the other).
   */
  public static final int TYPES_UNRELATED = 0;

  /**
   * The upper bound for all types in JML and BML i.e. \TYPE.
   */
  private static final JavaType TYPE = new JavaType();

  /**
   * A standard constructor for subclasses.
   */
  protected JavaType() {
    super(Code.JAVA_TYPE);
  }

  @Deprecated
  public static JavaType convert(final Type t) {
    if (t == Type.BOOLEAN) {
      return JavaBasicType.JAVA_BOOLEAN_TYPE;
    }
    if (t == Type.BYTE || t == Type.SHORT || t == Type.INT || t == Type.LONG) {
      return JavaBasicType.JAVA_INT_TYPE;
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
      return JavaBasicType.JAVA_INT_TYPE;
    }
    if (DisplayStyle.JT_BOOLEAN.equals(name)) {
      return JavaBasicType.JAVA_BOOLEAN_TYPE;
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
      return JavaBasicType.JAVA_INT_TYPE;
    }
    if (DisplayStyle.JT_BOOLEAN.equals(name) || "B".equals(name)) {
      return JavaBasicType.JAVA_BOOLEAN_TYPE;
    }
    if (DisplayStyle.TYPE_KWD.equals(name)) {
      return JavaType.TYPE;
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
   * @return type of JavaType, that is, {@link JavaBasicType#JavaType}.
   */
  protected JavaType checkType1() {
    return JavaBasicType.JavaType;
  }

  /**
   * Compares this type with given type.<br>
   * //TODO checking for subtypes currently not supported except \TYPE.
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
  public int compareTypes(final JavaType type) {
    if (type != this) {
      return IS_SUBTYPE;
    } else {
      return TYPES_EQUAL;
    }
  }

  /**
   * @return type of JavaType, that is,
   *     {@link JavaBasicType#JavaType}.
   */
  @Override
  public JavaType getType1() {
    return JavaBasicType.JavaType;
  }

  /**
   * Returns the string representation of the \TYPE expression.
   *
   * @param conf - see {@link BMLConfig}.
   * @return {@link DisplayStyle#RESULT_KWD}
   */
  protected String printCode1(BMLConfig conf) {
    return DisplayStyle.TYPE_KWD;
  }

  /**
   * @return simple String representation of this
   *     expression, for debugging only.
   */
  public String toString() {
    return DisplayStyle.TYPE_KWD;
  }

}
