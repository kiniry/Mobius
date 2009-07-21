package mobius.bmlvcgen.bml.debug;

import java.util.EnumSet;

import mobius.bmlvcgen.bml.FieldVisitor;
import mobius.bmlvcgen.bml.Field.AccessFlag;
import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.bml.types.TypePrinter;
import mobius.bmlvcgen.logging.Logger;
import mobius.bmlvcgen.util.StringUtil;

/**
 * A field visitor which writes information
 * about visited fields to a logger.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class LoggingFieldVisitor implements FieldVisitor {
  // Logger used for output.
  private final Logger logger;
  // Object used to convert types to strings.
  private final TypePrinter typePrinter;
  // Access flags of last visited field.
  private String lastFlags;
  // Name of last visited field.
  private String lastName;
  
  /**
   * Constructor.
   * @param logger Logger instance.
   */
  public LoggingFieldVisitor(final Logger logger) {
    typePrinter = new TypePrinter();
    this.logger = logger;
  }
  
  /** {@inheritDoc} */
  public void visitFlags(final EnumSet<AccessFlag> flags) {
    lastFlags = StringUtil.join(flags, ", ");
  }

  /** {@inheritDoc} */
  public void visitName(final String name) {
    lastName = name;
  }

  /** {@inheritDoc} */
  public void visitType(final Type t) {
    t.accept(typePrinter);
    logger.debug("Visited field: %1$s %2$s %3$s", 
                 lastFlags, lastName, 
                 typePrinter.getExternalName());
  }

}
