/**
 * Collection of smart strings for comparing strings in different cases.
 */
package utils.smart;

import java.util.List;
import java.util.Vector;


/**
 * Holds the contents of a generic parameter eg T extends someClass.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class GenericParameter extends SmartString {
  /** Stor the T, S or whatever only for consistency with existing code. */
  private final String my_dummy;
  /** Extending or implementing types. */
  private final List < SmartString > my_types;

  /**
   * Creates a new generic parameter.
   * @param a_name original string representation of this generic parameter
   * @param a_dummy the name of the dummy variable
   * @param some_types the types it extends, empty list if no constraints
   */
  public GenericParameter(final String a_name, final String a_dummy,
                          final List < SmartString > some_types) {
    super(a_name);
    my_dummy = a_dummy;
    if (some_types == null) {
      my_types = new Vector < SmartString > ();
    } else {
      my_types = some_types;
    }
  }


  /**
   * Get the dummy name.
   * @return the dummy name
   */
  public final String getDummyName() {
    return my_dummy;
  }


  /**
   * Get the types the parameter must extend.
   * @return possibly empty list of types
   */
  public final List < SmartString > getTypes() {
    return my_types;
  }

  /**
   * Compare two SmartStrings.
   * They can only match if they are of the same class.
   * @see java.lang.Comparable#compareTo(java.lang.Object)
   * @param an_other SmartString to compare
   * @return 0 is the two SmartStrings are equal
   */
  @Override
  public final int compareTo(final SmartString an_other) {
    if (an_other instanceof GenericParameter) {
      final GenericParameter other = (GenericParameter) an_other;
      if (my_types.size() != other.my_types.size()) {
        if (my_types.size() < other.my_types.size()) {
          return -1;
        } else if (my_types.size() > other.my_types.size()) {
          return 1;
        }
      }
      for (int i = 0; i < my_types.size(); i++) {
        final SmartString thisType = my_types.get(i);
        final SmartString otherType = other.my_types.get(i);
        if (thisType.compareTo(otherType) != 0) {
          return thisType.compareTo(otherType);
        }
      }
      return 0;
    } else {
      return new SmartString(my_string).compareToTyped(an_other);
    }
  }

  /**
   * Compared two GenericParameters based on the type dictionary.
   * @param an_other generic parameter to compare to
   * @return -1, 0 if they are equal, or 1
   */
  @Override
  public final int compareToTyped(final SmartString an_other) {
    if (an_other instanceof GenericParameter) {
      final GenericParameter other = (GenericParameter) an_other;
      if (my_types.size() == 1 && other.my_types.size() > 1) {
        for (final SmartString s : other.my_types) {
          if (s.compareToTyped(my_types.get(0)) == 0) {
            return 0;
          }
        }
        return -1;
      } else if (other.my_types.size() == 1 && my_types.size() > 1) {
        for (final SmartString s : my_types) {
          if (s.compareToTyped(other.my_types.get(0)) == 0) {
            return 0;
          }
        }
        return 1;
      } else if (my_types.size() != other.my_types.size()) {
        if (my_types.size() < other.my_types.size()) {
          return -1;
        } else if (my_types.size() > other.my_types.size()) {
          return 1;
        }
      }

      for (int i = 0; i < my_types.size(); i++) {
        final SmartString thisType = my_types.get(i);
        final SmartString otherType = other.my_types.get(i);
        if (thisType.compareToTyped(otherType) != 0) {
          return thisType.compareToTyped(otherType);
        }
      }
      return 0;
    } else {
      return new SmartString(my_string).compareToTyped(an_other);
    }
  }

  /**
   * Equals method.
   * @see java.lang.Object#equals(java.lang.Object)
   * @param some_obj object to compare to
   * @return true if objects are equal
   */
  @Override
  public final boolean equals(final Object some_obj) {
    //keep the default
    if (this == some_obj) {
      return true;
    }
    if (!(some_obj instanceof GenericParameter)) {
      return false;
    }
    //if we have null in either one, no comparison makes sense
    if (some_obj == null) {
      return false;
    }
    //Now comes our own comparison:
    final GenericParameter other = (GenericParameter) some_obj;
    if (this.compareTo(other) == 0) {
      return true;
    }
    return false;
  }

  /**
   * Whether two generic parameter are equal as far as typing is concerned.
   * @param some_obj generic parameter to compare to
   * @return true if they are type-equal
   */
  @Override
  public final boolean equalsTyped(final Object some_obj) {
    //keep the default
    if (this == some_obj) {
      return true;
    }
    if (!(some_obj instanceof GenericParameter)) {
      return false;
    }
    //if we have null in either one, no comparison makes sense
    if (some_obj == null) {
      return false;
    }
    //Now comes our own comparison:
    final GenericParameter other = (GenericParameter) some_obj;
    if (this.compareToTyped(other) == 0) {
      return true;
    }
    return false;
  }
}
