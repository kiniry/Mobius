package mobius.bmlvcgen.bml.debug;

import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.bml.types.Type;

/**
 * Printer for preconditions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class PreExprPrinter 
  extends ExprPrinter<PreExprVisitor> implements PreExprVisitor {

  /** {@inheritDoc} */
  @Override
  protected PreExprPrinter getThis() {
    return this;
  }

  /** {@inheritDoc} */
  public void arg(final int i, final String name, 
                  final Type type) {
    if (name == null) {
      append("#arg" + i);
    } else {
      append(name);
    }
  }
}
