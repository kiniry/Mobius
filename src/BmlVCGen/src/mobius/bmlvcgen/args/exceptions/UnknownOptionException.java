package mobius.bmlvcgen.args.exceptions;

/**
 * Exception thrown when unrecognized option is found in argument list.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class UnknownOptionException extends ArgException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  private final String option;

  /**
   * Constructor.
   * @param option Unrecognized option (including '-' or '--').
   */
  public UnknownOptionException(final String option) {
    super("Unknown option: " + option);
    this.option = option;
  }

  /**
   * Constructor.
   * @param option Unrecognized option (including '-' or '--').
   * @param message Message.
   */
  public UnknownOptionException(final String option, final String message) {
    super(message);
    this.option = option;
  }

  /**
   * Constructor.
   * @param option Unrecognized option (including '-' or '--').
   * @param cause Cause (inner exception).
   */
  public UnknownOptionException(final String option, final Throwable cause) {
    super(cause);
    this.option = option;
  }

  /**
   * Constructor.
   * @param option Unrecognized option (including '-' or '--').
   * @param message Message.
   * @param cause Cause (inner exception).
   */
  public UnknownOptionException(final String option, final String message,
                                final Throwable cause) {
    super(message, cause);
    this.option = option;
  }

  /**
   * Get option text.
   * @return Option text (including '-' or '--').
   */
  public String getOption() {
    return option;
  }

}
