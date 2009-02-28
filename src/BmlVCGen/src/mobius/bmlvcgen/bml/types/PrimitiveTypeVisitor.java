package mobius.bmlvcgen.bml.types;

/**
 * Interface of objects capable of visiting
 * primitive java types.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface PrimitiveTypeVisitor {
  /** Visit byte. */
  void visitByte();
  /** Visit char. */
  void visitChar();
  /** Visit short. */
  void visitShort();
  /** Visit integer. */
  void visitInt();
  /** Visit long. */
  void visitLong();
  /** Visit float. */
  void visitFloat();
  /** Visit double. */
  void visitDouble();
  /** Visit boolean. */
  void visitBoolean();
}
