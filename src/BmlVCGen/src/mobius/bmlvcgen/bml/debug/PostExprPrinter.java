package mobius.bmlvcgen.bml.debug;

import mobius.bmlvcgen.bml.PostExprVisitor;
import mobius.bmlvcgen.bml.PreExprVisitor;
import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.util.Visitable;

/**
 * Printer for postconditions.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class PostExprPrinter 
  extends ExprPrinter<PostExprVisitor> implements PostExprVisitor {
  private final PreExprPrinter prePrinter;
  
  /**
   * Constructor.
   * @param prePrinter Object used to print old expressions.
   */
  public PostExprPrinter(final PreExprPrinter prePrinter) {
    this.prePrinter = prePrinter;
  }
  
  /** {@inheritDoc} */
  @Override
  protected PostExprPrinter getThis() {
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

  /** {@inheritDoc} */
  public <Expr extends Visitable<? super PreExprVisitor>>
  void old(final Expr expr) {
    //
    prePrinter.clear();
    expr.accept(prePrinter);
    append("\\old(");
    append(prePrinter.getText());
    append(")");
  }

  /** {@inheritDoc} */
  public void result() {
    append("\\result");
  }
}
