package mobius.bmlvcgen.args;

/**
 * Implements a boolean flag which can be set/unset using command-line options.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class Flag {
  private boolean value;

  /**
   * Constructor.
   * @param initialValue Initial value of the flag.
   */
  public Flag(final boolean initialValue) {
    value = initialValue;
  }

  /**
   * Get option which can be used to 
   * set this flag to given value.
   * @param shortName Option name (short).
   * @param val Value.
   * @return Option instance.
   */
  public Option getOption(final char shortName, final boolean val) {
    return new FlagOption(this, val, shortName);
  }

  /**
   * Get option which can be used to 
   * set this flag to given value.
   * @param longName Option name (long).
   * @param val Value.
   * @return Option instance.
   */
  public Option getOption(final String longName, final boolean val) {
    return new FlagOption(this, val, longName);
  }

  /**
   * Get option which can be used to 
   * set this flag to given value.
   * @param shortName Option name (short).
   * @param longName Option name (long).
   * @param val Value.
   * @return Option instance.
   */
  public Option getOption(final char shortName, final String longName,
                          final boolean val) {
    return new FlagOption(this, val, shortName, longName);
  }

  /**
   * Get flag value.
   * @return Flag value.
   */
  public boolean getValue() {
    return value;
  }

  /**
   * Set flag value.
   * @param value Flag value.
   */
  public void setValue(final boolean value) {
    this.value = value;
  }
}
