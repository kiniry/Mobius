package mobius.bmlvcgen.args;

/**
 * An option with (required) string value.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class StringOption extends AbstractOption {
  private String value;

  /**
   * Constructor.
   * @param shortName Option name (short).
   */
  public StringOption(final char shortName) {
    super(shortName, Arity.REQUIRED_ARGUMENT);
  }

  /**
   * Constructor.
   * @param longName Option name (long).
   */
  public StringOption(final String longName) {
    super(longName, Arity.REQUIRED_ARGUMENT);
  }

  /**
   * Constructor.
   * @param shortName Option name (short).
   * @param longName Option name (long).
   */
  public StringOption(final char shortName, final String longName) {
    super(shortName, longName, Arity.REQUIRED_ARGUMENT);
  }

  /**
   * Set option value.
   * @param value Value.
   */
  public void setValue(final String value) {
    this.value = value;
  }

  /**
   * Get option value.
   * @return Value.
   */
  public String getValue() {
    return value;
  }

}
