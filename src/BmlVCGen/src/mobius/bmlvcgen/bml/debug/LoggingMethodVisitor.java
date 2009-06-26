package mobius.bmlvcgen.bml.debug;

import java.util.EnumSet;

import mobius.bmlvcgen.bml.AssertExprVisitor;
import mobius.bmlvcgen.bml.AssertType;
import mobius.bmlvcgen.bml.MethodName;
import mobius.bmlvcgen.bml.MethodSpec;
import mobius.bmlvcgen.bml.MethodVisitor;
import mobius.bmlvcgen.bml.Method.AccessFlag;
import mobius.bmlvcgen.bml.types.TypePrinter;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.util.StringUtil;
import mobius.bmlvcgen.util.Visitable;

/**
 * A method visitor which writes information
 * about visited methods to a logger.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class LoggingMethodVisitor implements MethodVisitor {
  // Logger used for output.
  private final Logger logger;
  // Object used to print method names and types.
  private final MethodNamePrinter namePrinter;
  // Object used to log specification cases
  private final LoggingSpecVisitor specPrinter;
  // Object used to convert assertions to strings.
  private final AssertExprPrinter assertPrinter;
  // Builder used to construct output.
  private final StringBuilder builder;
  // Object used to print types.
  private final TypePrinter typePrinter;
  
  /**
   * Constructor.
   * @param logger Logger instance.
   */
  public LoggingMethodVisitor(final Logger logger) {
    this.logger = logger;
    namePrinter = new MethodNamePrinter();
    builder = new StringBuilder();
    specPrinter = new LoggingSpecVisitor(logger);
    assertPrinter = new AssertExprPrinter(new PreExprPrinter());
    typePrinter = new TypePrinter();
  }

  /** {@inheritDoc} */
  public void visitFlags(final EnumSet<AccessFlag> flags) {
    builder.delete(0, builder.length());
    builder.append(StringUtil.join(flags, " "));
  }

  /** {@inheritDoc} */
  public void visitName(final MethodName name) {
    name.accept(namePrinter);
    if (builder.length() > 0) {
      builder.append(" ");
    }
    builder.append(namePrinter.getText());
  }
  
  /** {@inheritDoc} */
  public void beginSpecs() {
    // EMPTY
  }
  
  /** {@inheritDoc} */
  public void visitSpecification(final MethodSpec spec) {
    spec.accept(specPrinter);
  }
  
  /** {@inheritDoc} */
  public void endSpecs() {
    //
  }

  /** {@inheritDoc} */
  public void beginAssertions() {
    // 
  }

  /** {@inheritDoc} */
  public void visitAssertion(final int i, 
      final AssertType type,
      final Visitable<? super AssertExprVisitor> expr) {
    expr.accept(assertPrinter);
    switch (type) {
      case POST:
        logger.debug("Assertion after instruction %d: %s", i, 
                     assertPrinter.getText());
        break;
      case PRE:
        logger.debug("Assertion before instruction %d: %s", i, 
                     assertPrinter.getText());
        break;
      default: 
        assert (false); 
        break;
    }
  }
  
  /** {@inheritDoc} */
  public void endAssertions() {
    //
  }

  /** {@inheritDoc} */
  public void beginLocals(final int maxLocals) {
    // Print method name.
    logger.debug(builder.toString());
    logger.debug("LOCALS (%d)", maxLocals);    
  }

  /** {@inheritDoc} */
  public void visitLocal(
      final mobius.bmlvcgen.bml.LocalVariable var) {
    var.getType().accept(typePrinter);
    logger.debug("Local variable: %s, index %d, " + 
                 "from %d to %d, type %s",
                 var.getName(), var.getIndex(),
                 var.getStart(), var.getEnd(), 
                 typePrinter.getExternalName());
  }
  
  /** {@inheritDoc} */
  public void endLocals() {
    logger.debug("END LOCALS");
  }



}
