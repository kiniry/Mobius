package utils.smart;




/**
 * SmartString for class names.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class TypeSmartString extends SmartString {

  /**
   * Creates a new ClassSmartString representing the given string.
   * @param a_name string that is to be represented as a ClassSmartString
   */
  public TypeSmartString(final String a_name) {
    super(a_name);
  }

  /**
   * Creates a new empty ClassSmartString.
   */
  public TypeSmartString() {
    super();
  }

  /**
   * Removes all reduntant information from the string so that only the
   * information necessary for identification is left.
   * @see utils.smart.SmartString#trimSmartString()
   * @return trimmed representation of this string
   */
  @Override
  protected final String trimSmartString() {
    //the usual convention...
    String string = super.trimSmartString();

    //...plus some more
    int index = string.lastIndexOf('.');
    if (index != -1 && index != string.length()) {
      string = string.substring(index + 1);
    }
    if (string.contains("$")) { //$NON-NLS-1$
      index = string.lastIndexOf('$');
      if (index != -1 && index != string.length()) {
        string = string.substring(index + 1);
      }
    }
    return string;
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
  public int compareToTyped(final SmartString an_other) {
    if (an_other instanceof WildcardSmartString) {
      return an_other.compareToTyped(this);
    }
    if (an_other instanceof TypeSmartString) {
      final TypeSmartString a_string = (TypeSmartString) an_other;
      return new SmartString(getSimpleName()).
      compareToTyped(new SmartString(a_string.getSimpleName()));
    } else {
      return trimSmartString().compareTo(an_other.trimSmartString());
    }
  }

  /**
   * Compares two SmartStrings based on the dictionary of types.
   * @param an_obj object to compare
   * @return true if they are equal as far as typing is concerned
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
    final TypeSmartString a_string = (TypeSmartString) an_obj;

    if (this.compareToTyped(a_string) == 0) {
      return true;
    }
    return false;
  }

  /**
   * Make copy.
   * @see utils.smart.SmartString#makeCopy()
   * @return copy
   */
  @Override
  public SmartString makeCopy() {
    return new TypeSmartString(my_string);
  }

  /**
   * Get the original full string.
   * @return full string
   */
  public SmartString toQualifiedString() {
    return new SmartString(my_string);
  }

  /**
   * Get a simple class name, that is the last part
   * after the last '.' and last '$'.
   * @return simple class name
   */
  public String getSimpleName() {
    String name = my_string;
    int index = name.lastIndexOf('.');
    if (index != -1 && index != name.length()) {
      name = name.substring(index + 1);
    }
    index = name.lastIndexOf('$');
    if (index != -1 && index != name.length()) {
      name = name.substring(index + 1);
    }

    return name;
  }



}
