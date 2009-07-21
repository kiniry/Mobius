package mobius.bmlvcgen.bml;

/**
 * Method name and type.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface MethodName {
  /**
   * Visit this object.
   * @param v Visitor.
   */
  void accept(MethodNameVisitor v);
}
