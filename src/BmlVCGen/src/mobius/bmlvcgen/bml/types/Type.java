package mobius.bmlvcgen.bml.types;

/**
 * Interface of types.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface Type {  
  /**
   * Visit this type.
   * @param v Visitor.
   */
  void accept(TypeVisitor v);
}
