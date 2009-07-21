package mobius.bmlvcgen.bml.bmllib;

import mobius.bmlvcgen.bml.PostExprVisitor;
import mobius.bmlvcgen.util.Visitable;

/**
 * Wrapper for bmllib result expression.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class ResultExpr implements Visitable<PostExprVisitor> {

  /** {@inheritDoc} */
  public void accept(final PostExprVisitor visitor) {
    visitor.result();
  }

}
