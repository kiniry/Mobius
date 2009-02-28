package mobius.bmlvcgen.bml.types;

/**
 * Interface of objects capable of visiting
 * java reference types.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface RefTypeVisitor {
  /** 
   * Visit reference type.
   * @param clazz Fully qualified class name 
   * (with dots as separators).
   */
  void visitRefType(String clazz);
}
