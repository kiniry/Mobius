package mobius.bmlvcgen.bml.debug;

import mobius.bmlvcgen.bml.AssertExprVisitor;
import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.util.Visitable;

/**
 * Printer for preconditions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class AssertExprPrinter 
  extends ExprPrinter<AssertExprVisitor> 
  implements AssertExprVisitor {

  private final PreExprPrinter prePrinter;
  
  /**
   * Constructor.
   * @param prePrinter Object used to print old expressions.
   */
  public AssertExprPrinter(final PreExprPrinter prePrinter) {
    this.prePrinter = prePrinter;
  }
  
  /** {@inheritDoc} */
  @Override
  protected AssertExprPrinter getThis() {
    return this;
  }

  /** {@inheritDoc} */
  public void local(final int i, final String name, 
                  final Type type) {
    if (name == null) {
      append("#arg" + i);
    } else {
      append(name);
    }
  }
  
  /** {@inheritDoc} */
  public <Expr extends Visitable<? super PreExprVisitor>>
  void aold(final Expr expr) {
    prePrinter.clear();
    expr.accept(prePrinter);
    append("\\old(");
    append(prePrinter.getText());
    append(")");
  }
}
