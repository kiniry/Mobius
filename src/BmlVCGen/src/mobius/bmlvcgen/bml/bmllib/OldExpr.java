package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.PostExprVisitor;
import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.util.Visitable;

/**
 * Wrapper for bmllib old expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class OldExpr implements Visitable<PostExprVisitor> {
  final Visitable<PreExprVisitor> arg;
  
  /**
   * Constructor.
   * @param arg Argument of 'old()' call.
   */
  public OldExpr(final Visitable<PreExprVisitor> arg) {
    this.arg = arg;
  }
  
  /** {@inheritDoc} */
  public void accept(final PostExprVisitor visitor) {
    visitor.old(arg);
  }

}
