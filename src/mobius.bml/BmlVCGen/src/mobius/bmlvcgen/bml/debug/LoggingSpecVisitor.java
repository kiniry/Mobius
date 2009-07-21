package mobius.bmlvcgen.bml.debug;

import mobius.bmlvcgen.bml.MethodSpecVisitor;
import mobius.bmlvcgen.bml.PostExprVisitor;
import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.util.Visitable;

/**
 * Specification visitor which logs all
 * expressions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class LoggingSpecVisitor implements MethodSpecVisitor {
  // Logger to use.
  private final Logger logger;
  // Printer for preconditions.
  private final PreExprPrinter prePrinter;
  // Printer for postconditions.
  private final PostExprPrinter postPrinter;
  
  /**
   * Constructor.
   * @param logger Logger.
   */
  public LoggingSpecVisitor(final Logger logger) {
    this.logger = logger;
    prePrinter = new PreExprPrinter();
    postPrinter = new PostExprPrinter(prePrinter);
  }

  /** {@inheritDoc} */
  public void visitPrecondition(
      final Visitable<? super PreExprVisitor> pre) {
    prePrinter.clear();
    pre.accept(prePrinter);
    logger.debug(" Specification case: ");
    logger.debug("  Precondition: %1$s", prePrinter.getText());
  }

  /** {@inheritDoc} */
  public void visitPostcondition(
      final Visitable<? super PostExprVisitor> post) {
    postPrinter.clear();
    post.accept(postPrinter);
    logger.debug("  Postcondition: %1$s", postPrinter.getText());
  }

  /** {@inheritDoc} */
  public void visitSignals(
    final String exc, 
    final Visitable<? super PostExprVisitor> expr) {
    // TODO Auto-generated method stub
  }
  
}
