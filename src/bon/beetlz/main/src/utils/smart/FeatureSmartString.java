
package utils.smart;

import java.util.List;
import java.util.Vector;

/**
 * SmartString for feature names.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class FeatureSmartString extends SmartString {
  /** Prefixes of variables to be ignored/recognized. */
  private static List < String > prefixes = new Vector < String > ();

  /**
   * Creates a new FeatureSmartString representing the given string.
   * @param the_name string that is to be represented as a FeatureSmartString
   */
  public FeatureSmartString(final String the_name) {
    super(the_name);
  }

  /**
   * Create a string representing the \everything frame constraint.
   * @return everything-string
   */
  public static FeatureSmartString everything() {
    return new FeatureSmartString("\\everything"); //$NON-NLS-1$
  }

  /**
   * Create a string representing the \nothing frame constraint.
   * @return nothing-string
   */
  public static FeatureSmartString nothing() {
    return new FeatureSmartString("\\nothing"); //$NON-NLS-1$
  }

  /**
   * Removes all reduntant information from the string so that only the
   * information necessary for identification is left.
   * 'get', 'has' and 'is' prefixes are being removed, as well as the
   * the formatting done by the SmartString superclass.
   * @see utils.smart.SmartString#trimSmartString()
   * @return trimmed representation of this string
   */
  @Override
  protected final String trimSmartString() {
    //the usual convention + some more
    return super.trimSmartString();
  }

  /**
   * Equals with type comparison.
   * @see utils.smart.SmartString#equalsTyped(java.lang.Object)
   * @param an_obj object to compare to
   * @return true if the objects are equals
   */
  @Override
  public boolean equalsTyped(final Object an_obj) {
    if (this == an_obj) {
      return true;
    }
    if ((an_obj == null) || (an_obj.getClass() != this.getClass())) {
      return false;
    }

    // object must be SmartString at this point
    final FeatureSmartString a_string = (FeatureSmartString) an_obj;

    if (this.compareToTyped(a_string) == 0) {
      return true;
    }
    return false;
  }

  /**
   * Compare this string to another one.
   * @see utils.smart.SmartString#compareToTyped(utils.smart.SmartString)
   * @param an_other string to compare to
   * @return 0 if the strings are equal
   */
  @Override
  public int compareToTyped(final SmartString an_other) {
    if (an_other instanceof FeatureSmartString) {
      final FeatureSmartString a_string = (FeatureSmartString) an_other;
      String this_string = my_string;
      for (final String p : prefixes) {
        if (this_string.startsWith(p)) {
          this_string = this_string.substring(p.length());
        }
      }
      String other_string = a_string.my_string;
      for (final String p : prefixes) {
        if (other_string.startsWith(p)) {
          other_string = other_string.substring(p.length());
        }
      }
      return new SmartString(this_string).
      compareToTyped(new SmartString(other_string));
    } else {
      return trimSmartString().compareTo(an_other.trimSmartString());
    }

  }

  /**
   * Set the prefixes to ignore.
   * @param the_prefixes prefixes to be ignored
   */
  public static void setPrefixes(final List < String > the_prefixes) {
    prefixes = the_prefixes;
  }
}
