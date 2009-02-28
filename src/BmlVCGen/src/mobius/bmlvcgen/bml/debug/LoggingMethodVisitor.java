package mobius.bmlvcgen.bml.debug;

import java.util.EnumSet;

import mobius.bmlvcgen.bml.MethodName;
import mobius.bmlvcgen.bml.MethodSpec;
import mobius.bmlvcgen.bml.MethodVisitor;
import mobius.bmlvcgen.bml.Method.AccessFlag;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.util.StringUtil;

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
  // Builder used to construct output.
  private final StringBuilder builder;
  
  /**
   * Constructor.
   * @param logger Logger instance.
   */
  public LoggingMethodVisitor(final Logger logger) {
    this.logger = logger;
    namePrinter = new MethodNamePrinter();
    builder = new StringBuilder();
    specPrinter = new LoggingSpecVisitor(logger);
  }

  /** {@inheritDoc} */
  @Override
  public void visitFlags(final EnumSet<AccessFlag> flags) {
    builder.delete(0, builder.length());
    builder.append(StringUtil.join(flags, " "));
  }

  /** {@inheritDoc} */
  @Override
  public void visitName(final MethodName name) {
    name.accept(namePrinter);
    if (builder.length() > 0) {
      builder.append(" ");
    }
    builder.append(namePrinter.getText());
  }
  
  /** {@inheritDoc} */
  @Override
  public void beginSpecs() {
    logger.debug(builder.toString());
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitSpecification(final MethodSpec spec) {
    spec.accept(specPrinter);
  }
  
  /** {@inheritDoc} */
  @Override
  public void endSpecs() {
    
  }

}
