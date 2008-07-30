package annot.bcexpression.javatype;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.Type;

import annot.textio.BMLConfig;

/**
 * This class represents an array type.
 * Use {@link #getSingleType()} to get single element's type.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class JavaArrayType extends JavaType {

  /**
   * Original (BCEL's) type representation.
   */
  private final Type bcelType;

  /**
   * Type's (BCEL) signature, eg. "[I".
   */
  private final String signature;

  /**
   * Single element's (bmllib's) type.
   */
  private JavaType type;

  /**
   * A standard constructor.
   *
   * @param signature - a BCEL's type signature. Can be
   *     obtained using {@link Type#getSignature()} method.
   */
  public JavaArrayType(final String signature) {
    this.signature = signature;
    this.bcelType = Type.getType(signature);
    if (this.bcelType instanceof ArrayType) {
      final ArrayType at = (ArrayType) this.bcelType;
      final Type et = at.getElementType();
      final String subsig = et.getSignature();
      this.type = JavaType.getJavaType(subsig);
    }
  }

  @Override
  public int compareTypes(final JavaType type) {
    if (type == JavaReferenceType.ANY) {
      return TYPES_EQUAL;
    }
    if (type instanceof JavaArrayType) {
      final JavaArrayType rt = (JavaArrayType) type;
      if (this.signature.equals(rt.getSignature())) {
        return TYPES_EQUAL;
      }
    }
    return TYPES_UNRELATED;
  }

  /**
   * Original (BCEL's) type representation.
   */
  public Type getBcelType() {
    return this.bcelType;
  }

  /**
   * @return Type's (BCEL) signature, eg. "[I".
   */
  public String getSignature() {
    return this.signature;
  }

  /**
   * @return Single element's (bmllib's) type.
   */
  public JavaType getSingleType() {
    return this.type;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return this.type.printCode(conf) + "[]";
  }

  @Override
  public String toString() {
    return this.signature;
  }

}
