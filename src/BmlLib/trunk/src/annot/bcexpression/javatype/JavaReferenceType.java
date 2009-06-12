package annot.bcexpression.javatype;

import annot.io.AttributeWriter;
import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class describes any non-basic Java type.
 * It only stores type's signature.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class JavaReferenceType extends JavaType {

  /**
   * Type of null, for example.
   */
  public static final JavaReferenceType ANY = new JavaReferenceType("Object");

  /**
   * A type's signature. It can be any String, currently
   * its value is never parsed into other structures
   * in this library.
   */
  private final String signature;

  /**
   * A standard constructor.
   *
   * @param asignature - type's signature.
   */
  public JavaReferenceType(final String asignature) {
    this.signature = asignature;
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
  public int compareTypes(final JavaType type) {
    if (this.signature == null) {
      throw new RuntimeException("signature == null, what does it mean?");
    }
    if (type == ANY) {
      return TYPES_EQUAL;
    }
    if (type instanceof JavaReferenceType) {
      final JavaReferenceType rt = (JavaReferenceType) type;
      if (this.signature.equals(rt.getSignature())) {
        return TYPES_EQUAL;
        //TODO check for subtypes
      }
    }
    return TYPES_UNRELATED;
  }

  /**
   * @return the fully qualified type name as stored in constant pool.
   */
  public String getSignature() {
    return this.signature;
  }

  /**
   * Returns the string representation of the expression. This is the
   * string with the fully qualified type name as stored in constant pool.
   *
   * @param conf - see {@link BMLConfig}.
   * @return {@link DisplayStyle#RESULT_KWD}
   */
  protected String printCode1(final BMLConfig conf) {
    return this.signature;
  }

  /**
   * @return simple String representation of this
   *     expression, for debugging only.
   */
  public String toString() {
    return this.signature;
  }

  /**
   * Writes this expression to the AttributeWirter.
   *
   * @param aw - stream to save the type to
   */
  public void write(final AttributeWriter aw) {
    aw.writeByte(Code.JAVA_TYPE);
    final int cpIndex = aw.findConstant(this.signature);
    aw.writeShort(cpIndex);
  }

}
