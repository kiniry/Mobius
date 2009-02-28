package mobius.bmlvcgen.args.exceptions;

import java.util.Collection;
import java.util.Iterator;

import mobius.bmlvcgen.args.AbstractOption;
import mobius.bmlvcgen.args.Option;

/**
 * Exception thrown when a required argument is missing from command line.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class ArgMissingException extends ArgException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  private final Collection<Option> missingArguments;
  
  /**
   * Constructor.
   * @param missingArguments Collection of missing arguments.
   */
  public ArgMissingException(final Collection<Option> missingArguments) {
    super("Missing arguments: " + join(missingArguments));
    this.missingArguments = missingArguments;
  }

  /**
   * Constructor.
   * @param missingArguments Collection of missing arguments.
   * @param msg Message.
   */
  public ArgMissingException(final Collection<Option> missingArguments,
                             final String msg) {
    super(msg);
    this.missingArguments = missingArguments;
  }

  /**
   * Constructor.
   * @param missingArguments Collection of missing arguments.
   * @param cause Cause (inner exception).
   */
  public ArgMissingException(final Collection<Option> missingArguments,
                             final Throwable cause) {
    super(cause);
    this.missingArguments = missingArguments;
  }

  /**
   * Constructor.
   * @param missingArguments Collection of missing arguments.
   * @param msg Message.
   * @param cause Cause (inner exception).
   */
  public ArgMissingException(final Collection<Option> missingArguments,
                             final String msg, final Throwable cause) {
    super(msg, cause);
    this.missingArguments = missingArguments;
  }

  private static String join(final Collection<Option> opts) {
    final StringBuilder sb = new StringBuilder();
    final Iterator<Option> i = opts.iterator();
    while (i.hasNext()) {
      sb.append(AbstractOption.getOptionName(i.next()));
      if (i.hasNext()) {
        sb.append(", ");
      }
    }
    return sb.toString();
  }
  
  /**
   * Get all missing arguments.
   * @return Collection of missing arguments.
   */
  public Collection<Option> getMissingArguments() {
    return missingArguments;
  }

}
