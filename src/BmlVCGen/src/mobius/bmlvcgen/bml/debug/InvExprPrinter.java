package mobius.bmlvcgen.bml.debug;

import mobius.bmlvcgen.bml.InvExprVisitor;

/**
 * Printer for invariants.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class InvExprPrinter 
  extends ExprPrinter<InvExprVisitor> implements InvExprVisitor {

  /** {@inheritDoc} */
  @Override
  protected InvExprPrinter getThis() {
    return this;
  }

}
