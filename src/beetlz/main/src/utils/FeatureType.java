/**
 * Package for utility classes.
 */
package utils;

/**
 * Feature type enum.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public enum FeatureType {

  /** A query type feature. */
  QUERY("query"), //$NON-NLS-1$
  /** A command type feature. */
  COMMAND("command"), //$NON-NLS-1$
  /** A query and command type feature. */
  MIXED("mixed"), //$NON-NLS-1$
  /** Not identified type. */
  UNKNOWN("unknown"); //$NON-NLS-1$

  /** Holds the type. */
  private final String my_type;

  /**
   * Constructor.
   * @param a_type type
   */
  FeatureType(final String a_type) {
    this.my_type = a_type;
  }

  /**
   * Returns the value of the enum type.
   * @return string representation of enum type
   */
  public String getName() {
    return my_type;
  }
}
