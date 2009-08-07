package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.bml.types.TypeVisitor;
import annot.bcexpression.javatype.JavaArrayType;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;

/**
 * Wrapper for bmllib types.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class BmllibType implements Type {
  // Wrapped type.
  private final JavaType type;
  
  /**
   * Constructor.
   * @param type Type to be wrapped.
   */
  protected BmllibType(final JavaType type) {
    this.type = type;
  }

  /**
   * Wrap a bmllib type.
   * @param type Type to be wrapped.
   * @return Type instance.
   */
  public static Type getInstance(final JavaType type) {
    // TODO: Cache types.
    return new BmllibType(type);
  }
  
  /** {@inheritDoc} */
  public void accept(final TypeVisitor v) {
    if (type instanceof JavaBasicType) {
      processBasicType(v);
    } else if (type instanceof JavaArrayType) {
      processArrayType(v);
    } else {
      assert type instanceof JavaReferenceType;
      processRefType(v);
    }
  }
  
  // accept() for primitive types.
  private void processBasicType(final TypeVisitor v) {
    if (type == JavaBasicType.JAVA_INT_TYPE) {
      v.visitInt();
    } else if (type == JavaBasicType.JAVA_BOOLEAN_TYPE) {
      v.visitBoolean();
    } else {
      throw new UnsupportedOperationException(
         "Unknown bmllib basic type " + type.toString()
      );
    }
  }
  
  // accept() for array types.
  private void processArrayType(final TypeVisitor v) {
    final JavaArrayType arrayType = (JavaArrayType)type;
    v.visitArray(BmllibType.getInstance(arrayType.getSingleType()));
  }
  
  // accept() for object types.
  private void processRefType(final TypeVisitor v) {
    // TODO: Format of bmllib reference type
    // is not specified...     
    if (type == JavaReferenceType.ANY) {
      v.visitRefType("java.lang.Object");
    } else {
      v.visitRefType(type.toString());
    }
  }
}
