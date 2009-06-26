package mobius.bmlvcgen.bml.debug;

import java.util.EnumSet;

import mobius.bmlvcgen.bml.ClassVisitor;
import mobius.bmlvcgen.bml.Field;
import mobius.bmlvcgen.bml.InvExprVisitor;
import mobius.bmlvcgen.bml.Method;
import mobius.bmlvcgen.bml.ClassFile.AccessFlag;
import mobius.bmlvcgen.bml.ClassFile.Visibility;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.util.StringUtil;
import mobius.bmlvcgen.util.Visitable;

/**
 * A class visitor which writes information
 * about visited classes to a logger.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class LoggingClassVisitor implements ClassVisitor {
  // Logger used for output.
  private final Logger logger;
  // Field visitor.
  private final LoggingFieldVisitor fieldVisitor;
  // Method visitor.
  private final LoggingMethodVisitor methodVisitor;
  // Object used to print invariants.
  private final InvExprPrinter invPrinter;
  
  /**
   * Constructor.
   * @param logger Logger instance.
   */
  public LoggingClassVisitor(final Logger logger) {
    this.logger = logger;
    fieldVisitor = new LoggingFieldVisitor(logger);
    methodVisitor = new LoggingMethodVisitor(logger);
    invPrinter = new InvExprPrinter();
  }
  
  /** {@inheritDoc} */
  public void visitVersion(final int major, final int minor) {
    logger.debug("Classfile version: %1$d.%2$d", major, minor);
  }
  
  /** {@inheritDoc} */
  public void visitFlags(final EnumSet<AccessFlag> flags) {
    logger.debug("Access flags: %1$s", StringUtil.join(flags, ", "));
  }
  
  /** {@inheritDoc} */
  public void visitName(final String name) {
    logger.debug("Class name: %1$s", name);
  }
  
  /** {@inheritDoc} */
  public void visitSuperName(final String name) {
    if (name != null) {
      logger.debug("Superclass name: %1$s", name);
    }
  }
  
  /** {@inheritDoc} */
  public void beginInterfaces() {
    // do nothing.
  }
  
  /** {@inheritDoc} */
  public void visitInterface(final String name) {
    logger.debug("Implements interface: %1$s", name);
  }
  
  /** {@inheritDoc} */
  public void endInterfaces() {
    // do nothing.
  }
  
  /** {@inheritDoc} */
  public void beginInvariants() {
    // do nothing.
  }
  
  /** {@inheritDoc} */
  public void visitInvariant(
       final Visibility visibility, 
       final Visitable<? super InvExprVisitor> inv) {
    invPrinter.clear();
    inv.accept(invPrinter);
    logger.debug("%1$s invariant %2$s", visibility, 
                 invPrinter.getText());
  }
  
  /** {@inheritDoc} */
  public void endInvariants() {
    // do nothing.
  }
  
  /** {@inheritDoc} */
  public void beginFields() {
    // do nothing.
  }

  /** {@inheritDoc} */
  public void visitField(final Field field) {
    field.accept(fieldVisitor);
  }
  
  /** {@inheritDoc} */
  public void endFields() {
    // do nothing.
  }
  
  /** {@inheritDoc} */
  public void beginMethods() {
    // do nothing.
  }

  /** {@inheritDoc} */
  public void visitMethod(final Method method) {
    method.accept(methodVisitor);
  }
  
  /** {@inheritDoc} */
  public void endMethods() {
    // do nothing.
  }
}
