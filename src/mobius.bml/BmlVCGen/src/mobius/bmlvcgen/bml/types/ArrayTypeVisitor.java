package mobius.bmlvcgen.bml.types;

/**
 * Interface of objects capable of visiting
 * java array types.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface ArrayTypeVisitor {
  /**
   * Visit array type.
   * @param t Type of array elements.
   */
  void visitArray(Type t);
}
