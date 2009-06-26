package mobius.bmlvcgen.args;

/**
 * Option used to set the value of a flag.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class FlagOption extends AbstractOption {
  private final boolean value;

  private final Flag flag;

  /**
   * Constructor.
   * @param flag Flag to set.
   * @param value Value.
   * @param shortName Option name (short).
   */
  public FlagOption(final Flag flag, final boolean value, final char shortName) {
    super(shortName, Arity.NO_ARGUMENT);
    this.flag = flag;
    this.value = value;
  }

  /**
   * Constructor.
   * @param flag Flag to set.
   * @param value Value.
   * @param longName Option name (long).
   */
  public FlagOption(final Flag flag, 
                    final boolean value, 
                    final String longName) {
    super(longName, Arity.NO_ARGUMENT);
    this.flag = flag;
    this.value = value;
  }

  /**
   * Constructor.
   * @param flag Flag to set.
   * @param value Value.
   * @param shortName Option name (short).
   * @param longName Option name (long).
   */
  public FlagOption(final Flag flag, final boolean value, final char shortName,
                    final String longName) {
    super(shortName, longName, Arity.NO_ARGUMENT);
    this.flag = flag;
    this.value = value;
  }

  /** {@inheritDoc} */
  public void setValue(final String value) {
    assert (value == null);
    flag.setValue(this.value);
  }
}
