package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.types.TypeVisitor;

import org.apache.bcel.Constants;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

/**
 * Wrapper for BCEL types.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class BcelType implements mobius.bmlvcgen.bml.types.Type {
  /** Wrapped type. */
  private final Type type;
  
  /**
   * Constructor.
   * @param type Type to be wrapped.
   */
  protected BcelType(final Type type) {
    this.type = type;
  }

  /**
   * Factory method.
   * @param type Type to be wrapped.
   * @return BmllibType instance.
   */
  public static BcelType getInstance(final Type type) {
    // TODO: cache types.
    return new BcelType(type);
  }
  
  /**
   * Get wrapped type.
   * @return Type.
   */
  protected Type getType() {
    return type;
  }
  
  //CHECKSTYLE:OFF
  /** {@inheritDoc} */
  public void accept(final TypeVisitor v) {
    switch (type.getType()) {
      case Constants.T_BOOLEAN: v.visitBoolean(); break;
      case Constants.T_BYTE: v.visitByte(); break;
      case Constants.T_CHAR: v.visitChar(); break;
      case Constants.T_DOUBLE: v.visitDouble(); break;
      case Constants.T_FLOAT: v.visitFloat(); break;
      case Constants.T_INT: v.visitInt(); break;
      case Constants.T_LONG: v.visitLong(); break;
      case Constants.T_SHORT: v.visitShort(); break;
      case Constants.T_OBJECT: 
        v.visitRefType(((ObjectType)type).getClassName());
        break;
      case Constants.T_ARRAY:
        v.visitArray(
          new BcelType(((ArrayType)type).getElementType())
        );
      case Constants.T_VOID: // ?
      default:
        assert false;
        break;
    }
  }
//CHECKSTYLE:ON
}
