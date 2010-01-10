/**
 * Package with smart strings.
 */
package utils.smart;

import logic.BeetlzExpression.Nullity;
import main.Beetlz;
import utils.BConst;
import utils.BasicTypesDictionary;

/**
 * A special type of String that has rules defined under which normally
 * different String are regarded as equal. We need this functionality because of
 * BON and Java/JML have different naming standards. For example, BIGCAGE,
 * BIG_CAGE, Big_Cage, BigCage should all represent the same class name. <p> For
 * extending classes it is enough to override the trimSmartString() method since
 * hashCode and equals use that method to determine equality.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class SmartString implements Comparable < SmartString > {
  /** Dictionary of recognized types.*/
  private static BasicTypesDictionary my_dictionary = new BasicTypesDictionary();
  /**
   * Specifies whether this SmartString is by default non_null
   * of nullable.
   */
  private Nullity my_nullity;
  /** String to represent.  */
  protected final String my_string;

  /**
   * Creates a new SmartString from the String specified.
   * @param the_name string to represent
   */
  public SmartString(final String the_name) {
    if (the_name == null) {
      my_string = BConst.NULL_SMARTSTRING;
    } else {
      my_string = the_name;
    }
    my_nullity = null;
  }

  /**
   * Creates a default SmartString, with zero length string.
   * This is useful, so that we can require SmartString references to
   * be non-null.
   */
  public SmartString() {
    this.my_string = BConst.NULL_SMARTSTRING;
    my_nullity = null;
  }

  /**
   * Creates a SmartString representing the value 'void'
   * or 'null'.
   * @return Void SmartString
   */
  public static SmartString getVoid() {
    return new SmartString("void"); //$NON-NLS-1$
  }

  /**
   * Returns the original String representation of this SmartString.
   * @see java.lang.Object#toString()
   * @return original string this SmartString was created from
   */
  @Override
  public String toString() {
    return my_string;
  }

  /**
   * Creates a hash code based on the original string.
   * @see java.lang.Object#hashCode()
   * @return hash code
   */
  @Override
  public int hashCode() {
    final int prime = 31;
    final int seven = 7;
    int result = seven;
    result = prime * result + this.trimSmartString().hashCode();
    return result;
  }

  /**
   * Are these two objects equal.
   * @see java.lang.Object#equals(java.lang.Object)
   * @param an_other object to compare to
   * @return true if objects are equals
   */
  @Override
  public boolean equals(final Object an_other) {
    if (this == an_other) {
      return true;
    }
    if ((an_other == null) || (an_other.getClass() != this.getClass())) {
      return false;
    }
    // object must be SmartString at this point
    final SmartString a_string = (SmartString) an_other;
    if (this.compareTo(a_string) == 0) {
      return true;
    }
    return false;
  }

  /**
   * Compare two SmartStrings.
   * @see java.lang.Comparable#compareTo(java.lang.Object)
   * @param an_other other SmartString to compare to
   * @return 0 if SmartString are equal
   */
  @Override
  public int compareTo(final SmartString an_other) {
    return this.trimSmartString().compareTo(an_other.trimSmartString());
  }

  /**
   * Gives length of original string.
   * Probably only useful for checking if we have a default String of length 0.
   * @return length of this string
   */
  public final int length() {
    return this.my_string.length();
  }

  /**
   * Trim the SmartString to such a format, that contains only necessary
   * information.
   * @return trimmed SmartStrings
   */
  protected String trimSmartString() {
    String string = my_string.toLowerCase();
    string = string.replace("_", ""); //$NON-NLS-1$ //$NON-NLS-2$
    string.trim();
    return string;
  }

  /**
   * Copy this SmartString.
   * @return copy of this SmartString
   */
  public SmartString makeCopy() {
    return new SmartString(my_string);
  }

  /**
   * Set the basic type dictionary to be used.
   * @param a_dict basic types
   */
  public static void setDictionary(final BasicTypesDictionary a_dict) {
    my_dictionary = a_dict;
  }

  /* ********************************
   * Type comparing methods
   **********************************/

  /**
   * Compares two SmartStrings based on the dictionary of types.
   * @param an_other object to compare
   * @return true if they are equal as far as typing is concerned
   */
  public boolean equalsTyped(final Object an_other) {
    if (this == an_other) {
      return true;
    }
    if ((an_other == null) || (an_other.getClass() != this.getClass())) {
      return false;
    }
    // object must be SmartString at this point
    final SmartString a_string = (SmartString) an_other;
    if (this.compareToTyped(a_string) == 0) {
      return true;
    }
    return false;
  }

  /**
   * Compares two SmartStrings based on the dictionary of types.
   * Note: only this method needs to be overridden in subclasses for
   * correct working, and also only if the trimSmartString() method
   * is not sufficient for comparison.
   * @param an_other object to compare
   * @return true if they are equal as far as typing is concerned
   */
  public int compareToTyped(final SmartString an_other) {
    if (my_dictionary.matchTypes(this, an_other)) {
      return 0;
    }
    final String type = (String) Beetlz.getClassMap().get(my_string);
    if (type != null) {
      return an_other.my_string.compareTo(type);
    }
    return this.trimSmartString().compareTo(an_other.trimSmartString());
  }

  /**
   * Compares the original strings of the SmartStrings,
   * without any preprocessing.
   * @param an_other object to compare to
   * @return true if they are equal
   */
  public boolean equalsExactly(final SmartString an_other) {
    return my_string.equals(an_other.my_string);
  }

  /**
   * Get the default nullity of this SmartString.
   * @return nullity: non_null or nullable
   */
  public Nullity getNullity() {
    return my_nullity;
  }

  /**
   * Set the default nullity.
   * @param the_nullity nullity
   */
  public void setNullity(final Nullity the_nullity) {
    my_nullity = the_nullity;
  }
}
