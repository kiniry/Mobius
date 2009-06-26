package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.AssertExprVisitor;
import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.util.Visitable;

/**
 * Wrapper for bmllib old expressions in assertions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class AOldExpr implements Visitable<AssertExprVisitor> {
  final Visitable<PreExprVisitor> arg;
  
  /**
   * Constructor.
   * @param arg Argument of 'old()' call.
   */
  public AOldExpr(final Visitable<PreExprVisitor> arg) {
    this.arg = arg;
  }
  
  /** {@inheritDoc} */
  public void accept(final AssertExprVisitor visitor) {
    visitor.aold(arg);
  }

}
