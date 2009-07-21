package mobius.bmlvcgen.vcgen;

import mobius.bmlvcgen.bml.types.ResultTypeVisitor;
import mobius.bmlvcgen.bml.types.Type;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.ObjectType;

/**
 * A type visitor which creates BCEL types.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class TypeConverter implements ResultTypeVisitor {
  // Last type visited.
  private org.apache.bcel.generic.Type last;
  
  /**
   * Get last type visited.
   * @return Type converted to BCEL type.
   */
  public org.apache.bcel.generic.Type getType() {
    return last;
  }
  
  /** {@inheritDoc} */
  public void visitVoid() {
    last = BasicType.VOID;
  }

  /** {@inheritDoc} */
  public void visitBoolean() {
    last = BasicType.BOOLEAN;
  }

  /** {@inheritDoc} */
  public void visitByte() {
    last = BasicType.BYTE;
  }

  /** {@inheritDoc} */
  public void visitChar() {
    last = BasicType.CHAR;
  }

  /** {@inheritDoc} */
  public void visitDouble() {
    last = BasicType.DOUBLE;
  }

  /** {@inheritDoc} */
  public void visitFloat() {
    last = BasicType.FLOAT;
  }

  /** {@inheritDoc} */
  public void visitInt() {
    last = BasicType.INT;
  }

  /** {@inheritDoc} */
  public void visitLong() {
    last = BasicType.LONG;
  }

  /** {@inheritDoc} */
  public void visitShort() {
    last = BasicType.SHORT;
  }

  /** {@inheritDoc} */
  public void visitRefType(final String clazz) {
    last = new ObjectType(clazz);
  }

  /** {@inheritDoc} */
  public void visitArray(final Type t) {
    t.accept(this);
    last = new ArrayType(last, 1);
  }

}
