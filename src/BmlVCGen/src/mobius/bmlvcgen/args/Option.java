package mobius.bmlvcgen.args;

/**
 * Interface of objects used to describe command-line options (and hold their
 * values).
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface Option {
  /** Number of arguments of an option. */
  static enum Arity {
    /** No argument. */
    NO_ARGUMENT,
    /** Optional argument. */
    OPTIONAL_ARGUMENT,
    /** Required argument. */
    REQUIRED_ARGUMENT
  }

  /** 
   * Get number of arguments of this option.
   * @return Option arity.
   */
  Arity getArity();

  /**
   * Short name of this option. If this option has no short
   * name, null should be returned.
   * @return Short name or null.
   */
  Character getShortName();

  /**
   * Long name of this option. If this option has no long
   * name, null should be returned.
   * @return Long name or null.
   */
  String getLongName();

  /**
   * Callback called when this option is encountered
   * in an argument list.
   * @param value Option value - null if not set.
   * @throws IllegalArgumentException If the value is not valid
   *                               for this option.
   */
  void setValue(String value);
}
