package mobius.bmlvcgen.args;

/**
 * Base class of options.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public abstract class AbstractOption implements Option {
  private final Arity arity;

  private final Character shortName;

  private final String longName;

  /**
   * Constructor for options with no long name.
   * @param shortName Short name.
   * @param arity Option arity.
   */
  protected AbstractOption(final char shortName, final Arity arity) {
    this.shortName = Character.valueOf(shortName);
    longName = null;
    this.arity = arity;
  }

  /**
   * Constructor for options with no short name.
   * @param longName Long name.
   * @param arity Option arity.
   */
  protected AbstractOption(final String longName, final Arity arity) {
    shortName = null;
    this.longName = longName;
    this.arity = arity;
  }

  /**
   * Constructor for options with both long and short name.
   * @param shortName Short name.
   * @param longName Long name.
   * @param arity Option arity.
   */
  protected AbstractOption(final char shortName, final String longName,
                           final Arity arity) {
    this.shortName = Character.valueOf(shortName);
    this.longName = longName;
    this.arity = arity;
  }

  
  /**
   * Simple utility method to convert option to string.
   * @param opt Option.
   * @return String representation of option.
   */
  public static final String getOptionName(final Option opt) {
    if (opt.getLongName() == null || "".equals(opt.getLongName())) {
      return "-" + String.valueOf(opt.getShortName());
    } else {
      return "--" + opt.getLongName();
    }
  }

  /** {@inheritDoc} */
  public Arity getArity() {
    return arity;
  }

  /** {@inheritDoc} */
  public Character getShortName() {
    return shortName;
  }

  /** {@inheritDoc} */
  public String getLongName() {
    return longName;
  }

}
