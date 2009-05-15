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
  @Override
  public void visitVoid() {
    last = BasicType.VOID;
  }

  /** {@inheritDoc} */
  @Override
  public void visitBoolean() {
    last = BasicType.BOOLEAN;
  }

  /** {@inheritDoc} */
  @Override
  public void visitByte() {
    last = BasicType.BYTE;
  }

  /** {@inheritDoc} */
  @Override
  public void visitChar() {
    last = BasicType.CHAR;
  }

  /** {@inheritDoc} */
  @Override
  public void visitDouble() {
    last = BasicType.DOUBLE;
  }

  /** {@inheritDoc} */
  @Override
  public void visitFloat() {
    last = BasicType.FLOAT;
  }

  /** {@inheritDoc} */
  @Override
  public void visitInt() {
    last = BasicType.INT;
  }

  /** {@inheritDoc} */
  @Override
  public void visitLong() {
    last = BasicType.LONG;
  }

  /** {@inheritDoc} */
  @Override
  public void visitShort() {
    last = BasicType.SHORT;
  }

  /** {@inheritDoc} */
  @Override
  public void visitRefType(final String clazz) {
    last = new ObjectType(clazz);
  }

  /** {@inheritDoc} */
  @Override
  public void visitArray(final Type t) {
    t.accept(this);
    last = new ArrayType(last, 1);
  }

}
