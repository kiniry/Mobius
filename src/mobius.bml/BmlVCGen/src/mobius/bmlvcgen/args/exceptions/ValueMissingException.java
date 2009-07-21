package mobius.bmlvcgen.args.exceptions;

import mobius.bmlvcgen.args.AbstractOption;
import mobius.bmlvcgen.args.Option;

/**
 * Exception thrown when a value was not supplied for an option that required
 * one.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class ValueMissingException extends ArgException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  private final Option option;

  /**
   * Constructor.
   * @param option Option which caused the problem.
   */
  public ValueMissingException(final Option option) {
    super("Missing value for option " + AbstractOption.getOptionName(option));
    this.option = option;
  }

  /**
   * Constructor.
   * @param option Option which caused the problem.
   * @param msg Message.
   */
  public ValueMissingException(final Option option, final String msg) {
    super(msg);
    this.option = option;
  }

  /**
   * Constructor.
   * @param option Option which caused the problem.
   * @param cause Cause (inner exception).
   */
  public ValueMissingException(final Throwable cause, final Option option) {
    super(cause);
    this.option = option;
  }

  /**
   * Constructor.
   * @param option Option which caused the problem.
   * @param msg Message.
   * @param cause Cause (inner exception).
   */
  public ValueMissingException(final Option option, final String msg,
                               final Throwable cause) {
    super(msg, cause);
    this.option = option;
  }

  /**
   * Get option which caused the problem.
   * @return Option.
   */
  public Option getOption() {
    return option;
  }
}
