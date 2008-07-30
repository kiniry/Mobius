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
   * it's value is never parsed into other structures
   * in this library.
   */
  private final String signature;

  /**
   * A standard constructor.
   *
   * @param signature - type's signature.
   */
  public JavaReferenceType(final String signature) {
    this.signature = signature;
  }

  @Override
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

  public String getSignature() {
    return this.signature;
  }

  /**
   * Returns this type's signature as a String
   * (the same String as given in constructor).
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    return this.signature;
  }

  @Override
  public String toString() {
    return this.signature;
  }

  @Override
  public void write(final AttributeWriter aw) {
    aw.writeByte(Code.JAVA_TYPE);
    final int cpIndex = aw.findConstant(this.signature);
    aw.writeShort(cpIndex);
  }

}
