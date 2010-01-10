package utils.smart;

import java.util.List;


/**
 * A SmartString that holds a parametrized type.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class ParametrizedSmartString extends SmartString {
  /** Complete string representation as appears in original source. */
  private final SmartString my_name;
  /** Parameters. */
  private final List < SmartString > my_params;

  /**
   * Creates a new parametrized string.
   * @param a_full_name string representation like it appear in the original
   * @param a_name outer type
   * @param the_parts parameter types
   */
  public ParametrizedSmartString(final String a_full_name, final SmartString a_name,
                                 final List < SmartString > the_parts) {
    super(a_full_name);
    my_name = a_name;
    my_params = the_parts;
  }

  /**
   * Removes all redundant information from the string so that only the
   * information necessary for identification is left.
   * 'get', 'has' and 'is' prefixes are being removed, as well as the
   * the formatting done by the SmartString superclass.
   * @see utils.smart.SmartString#trimSmartString()
   * @return trimmed representation of this string
   */
  @Override
  protected final String trimSmartString() {
    return super.trimSmartString();
  }

  /**
   * Number of parameters.
   * @return number of parameters
   */
  private int getNumberOfParameters() {
    return my_params.size();
  }

  /* ********************************
   * Type comparing methods
   **********************************/
  /**
   * Compares two SmartStrings based on the dictionary of types.
   * @param an_other object to compare
   * @return true if they are equal as far as typing is concerned
   */
  @Override
  public final int compareToTyped(final SmartString an_other) {
    if (an_other instanceof ParametrizedSmartString) {
      final ParametrizedSmartString a_string = (ParametrizedSmartString) an_other;
      if (this.getNumberOfParameters() < a_string.getNumberOfParameters()) {
        return -1;
      } else if (this.getNumberOfParameters() > a_string.getNumberOfParameters()) {
        return 1;
      } else if (my_name.compareToTyped(a_string.my_name) != 0) {
        return my_name.compareTo(a_string.my_name);
      } else {
        for (int i = 0; i < this.getNumberOfParameters(); i++) {
          if (my_params.get(i).compareToTyped(a_string.my_params.get(i)) != 0) {
            if (my_params.get(i).length() == 1 &&
                a_string.my_params.get(i).length() == 1) {
              continue;
            }
            return my_params.get(i).compareToTyped(a_string.my_params.get(i));
          }
        }
      }
    } else {
      return my_name.trimSmartString().compareTo(an_other.trimSmartString());
    }
    return 0;
  }

  /**
   * Compares two SmartStrings based on the dictionary of types.
   * @param an_other object to compare
   * @return true if they are equal as far as typing is concerned
   */
  @Override
  public final boolean equalsTyped(final Object an_other) {
    if (this == an_other) {
      return true;
    }
    if ((an_other == null) || (an_other.getClass() != this.getClass())) {
      return false;
    }
    // object must be SmartString at this point
    final ParametrizedSmartString a_string = (ParametrizedSmartString) an_other;
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
    return new ParametrizedSmartString(my_string, my_name, my_params);
  }


  /**
   * Get the type of this parametrized string.
   * @return type
   */
  public final SmartString getName() {
    return my_name;
  }

  /**
   * Get the parameters.
   * @return list of parameters
   */
  public final List < SmartString > getParams() {
    return my_params;
  }

  @Override
  public String toString() {
    return my_name + "[" + my_params + "]";
  }
  
  
}
