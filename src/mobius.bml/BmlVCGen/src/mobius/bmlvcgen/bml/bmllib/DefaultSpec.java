package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.MethodSpec;
import mobius.bmlvcgen.bml.MethodSpecVisitor;

/**
 * A specification object which is used if there
 * is no bml specification for a method.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class DefaultSpec implements MethodSpec {
  /** {@inheritDoc} */
  public void accept(final MethodSpecVisitor visitor) {
    visitor.visitPostcondition(new True());
    visitor.visitPrecondition(new True());
  }
}
