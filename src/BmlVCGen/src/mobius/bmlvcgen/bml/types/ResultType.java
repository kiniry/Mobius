package mobius.bmlvcgen.bml.types;

/**
 * Type of values returned by a method.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface ResultType {
  /**
   * Visit this type.
   * @param v Visitor.
   */
  void accept(ResultTypeVisitor v);
}
