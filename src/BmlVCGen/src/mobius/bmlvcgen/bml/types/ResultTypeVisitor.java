package mobius.bmlvcgen.bml.types;

/**
 * Interface of objects capable of visiting
 * return type of a method.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface ResultTypeVisitor extends TypeVisitor {
  /**
   * Visit void return type.
   */
  void visitVoid();
}
