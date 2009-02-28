package mobius.bmlvcgen.args.exceptions;

import mobius.bmlvcgen.args.AbstractOption;
import mobius.bmlvcgen.args.Option;

/**
 * Exception thrown when a value passed to an option is invalid.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class IllegalValueException extends ArgException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  private final Option option;

  private final String value;

  /**
   * Constructor.
   * @param option Option which caused the problem.
   * @param value Illegal value.
   */
  public IllegalValueException(final Option option, final String value) {
    super("Value " + value + " not valid for option " + 
          AbstractOption.getOptionName(option));
    this.option = option;
    this.value = value;
  }

  /**
   * Constructor.
   * @param option Option which caused the problem.
   * @param value Illegal value.
   * @param msg Message.
   */
  public IllegalValueException(final Option option, final String value,
                               final String msg) {
    super(msg);
    this.option = option;
    this.value = value;
  }

  /**
   * Constructor.
   * @param option Option which caused the problem.
   * @param value Illegal value.
   * @param cause Cause (inner exception).
   */
  public IllegalValueException(final Option option, final String value,
                               final Throwable cause) {
    super(cause);
    this.option = option;
    this.value = value;
  }

  /**
   * Constructor.
   * @param option Option which caused the problem.
   * @param value Illegal value.
   * @param msg Message.
   * @param cause Cause (inner exception).
   */
  public IllegalValueException(final Option option, final String value,
                               final String msg, final Throwable cause) {
    super(msg, cause);
    this.option = option;
    this.value = value;
  }

  /**
   * Get option which caused the problem.
   * @return Option.
   */
  public Option getOption() {
    return option;
  }

  /**
   * Get the illegal value.
   * @return Supplied value.
   */
  public String getValue() {
    return value;
  }
}
