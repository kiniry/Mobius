package mobius.bmlvcgen.bml;

/**
 * Method specification case.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface MethodSpec {
  /**
   * Visit this specification case.
   * @param v Visitor.
   */
  void accept(MethodSpecVisitor v);
}
