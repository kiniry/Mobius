package utils.smart;

import utils.BConst;



/**
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class WildcardSmartString extends SmartString implements Comparable < SmartString > {
  /** What type of wildcard is this. */
  private final WildcardType my_wildcard;
  /** Possible constraints. */
  private final SmartString my_bound;

  /**
   * Creates a new Wildcard.
   * @param a_name string representation as appears in original source
   * @param a_type type of wildcard
   * @param a_bound bounds
   */
  public WildcardSmartString(final String a_name, final WildcardType a_type,
                             final SmartString a_bound) {
    super(a_name);
    my_wildcard = a_type;
    my_bound = a_bound;
  }

  /**
   * Creates a BON default wildcard.
   * @return BON wildcard
   */
  public static WildcardSmartString getBONWildcard() {
    return new WildcardSmartString(BConst.ANY, WildcardType.NONE, new SmartString());
  }

  /**
   * Creates a Java default wildcard.
   * @return Java wildcard without bounds
   */
  public static WildcardSmartString getJavaWildcard() {
    return new WildcardSmartString("?", WildcardType.NONE, new SmartString()); //$NON-NLS-1$
  }

  /**
  Compares two SmartStrings based on the dictionary of types.
   * @param an_other object to compare
   * @return true if they are equal as far as typing is concerned
   */
  @Override
  public final int compareToTyped(final SmartString an_other) {
    if (an_other instanceof WildcardSmartString) {
      final WildcardSmartString a_string = (WildcardSmartString) an_other;
      if (my_wildcard == WildcardType.NONE &&
          a_string.my_wildcard == WildcardType.NONE) {
        return 0;
      }
      if (my_wildcard.compareTo(a_string.my_wildcard) != 0) {
        return my_wildcard.compareTo(a_string.my_wildcard);
      }
      return my_bound.compareToTyped(a_string.my_bound);

    } else if (an_other instanceof TypeSmartString) {
      return my_bound.compareToTyped(an_other);
    } else {
      return new SmartString(my_string).compareToTyped(an_other);
    }
  }

  /**
   * Compares two SmartStrings based on the dictionary of types.
   * @param an_obj object to compare
   * @return true if they are equal as far as typing is concerned
   */
  @Override
  public final boolean equalsTyped(final Object an_obj) {
    if (this == an_obj) {
      return true;
    }
    if ((an_obj == null) || (an_obj.getClass() != this.getClass())) {
      return false;
    }

    // object must be SmartString at this point
    final WildcardSmartString a_string = (WildcardSmartString) an_obj;

    if (this.compareToTyped(a_string) == 0) {
      return true;
    }
    return false;
  }

  /**
   * Make a copy of this string.
   * @see utils.smart.SmartString#makeCopy()
   * @return copy of this string
   */
  @Override
  public final SmartString makeCopy() {
    return new WildcardSmartString(my_string, my_wildcard, my_bound);
  }

  /**
   * Wildcard types.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public enum WildcardType {
    /** Two types of wildcards. */
    EXTENDS("extends"), SUPER("super"), NONE("none"); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$

    /**  */
    private final String my_modifier;
    /**
     *
     * @param a_name modifier type
     */
    WildcardType(final String a_name) {
      this.my_modifier = a_name;
    }

    /**
     * Returns the modifier in lower case written form.
     * @return String representation of modifier
     */
    public String getName() {
      return my_modifier;
    }

    /**
     * Returns the modifier in lower case written form.
     * @see java.lang.Enum#toString()
     * @return String representation of modifier
     */
    @Override
    public String toString() {
      return my_modifier;
    }

  }

  /**
   * Get constraint.
   * @return bound
   */
  public final SmartString getBound() {
    return my_bound;
  }

  /**
   * Get type of wildcard.
   * @return type of wildcard
   */
  public final WildcardType getType() {
    return my_wildcard;
  }
}
