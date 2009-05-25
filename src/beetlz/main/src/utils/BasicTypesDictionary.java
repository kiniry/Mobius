/**
 * Package with utility classes.
 */
package utils;


import java.util.List;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.Vector;

import utils.smart.SmartString;

/**
 * A dictionary for basic types that will be recognised.
 * It is extendable.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class BasicTypesDictionary {
  /**
   * Collection of mappings with the name of the mapping being also the key.
   */
  private final SortedMap < String, Mapping > my_mappings;

  /**
   * Constructor initializes the basic types mappings.
   */
  public BasicTypesDictionary() {
    my_mappings = new TreeMap < String, Mapping > ();
  }

  /**
   * Add a complete mapping.
   * @param a_name name of mapping, this is a unique identifier
   * @param some_bon_types Bon types of the mapping
   * @param some_java_types Java types of the mapping
   */
  public final void addMapping(final String a_name, final String[] some_bon_types,
                               final String[] some_java_types) {
    if (my_mappings.containsKey(a_name)) {
      my_mappings.get(a_name).addBonTypes(some_bon_types);
      my_mappings.get(a_name).addJavaTypes(some_java_types);
    } else {
      my_mappings.put(a_name, new Mapping(a_name, some_bon_types, some_java_types));
    }

  }

  /**
   * Goes through the mappings and tries to find a matching pair of
   * BON and Java types.
   * @param a_first_type SmartString representing the BON type
   * @param a_second_type SmartString representing a Java type
   * @return true if types match
   */
  public final boolean matchTypes(final SmartString a_first_type,
                                  final SmartString a_second_type) {
    return matchTypes(a_first_type.toString(), a_second_type.toString());
  }

  /**
   * Check if two types match.
   * @param a_first_type one type to match
   * @param a_second_type the other type to match
   * @return true if types match
   */
  public final boolean matchTypes(final String a_first_type,
                                  final String a_second_type) {
    for (final Mapping m : my_mappings.values()) {
      if (m.hasBonType(a_first_type) &&
          m.hasJavaType(a_second_type)) {
        return true;
      } else if (m.hasBonType(a_second_type) &&
          m.hasJavaType(a_first_type)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Get a mapping by its name, that is the BON part.
   * @param a_name name of mapping
   * @return mapping if present, otherwise null
   */
  public final String getBonToJavaMapping (final String a_name) {
    for (final Mapping m : my_mappings.values()) {
      final String map = m.getBonMapping(a_name);
      if (map != null) {
        return map;
      }
    }
    return null;
  }

  /**
   * Get a mapping by its name, that is its Java part.
   * @param a_name name of mapping
   * @return mapping if present, otherwise null
   */
  public final String getJavaToBonMapping (final String a_name) {
    for (final Mapping m : my_mappings.values()) {
      final String map = m.getJavaMapping(a_name);
      if (map != null) {
        return map;
      }
    }
    return null;
  }


  /**
   * Returns a String representation of the contents.
   * @see java.lang.Object#toString()
   * @return pretty-printed representation of all mappings.
   */
  @Override
  public final String toString() {
    String string = ""; //$NON-NLS-1$
    for (final Mapping m : my_mappings.values()) {
      string += m.toString() + "\n"; //$NON-NLS-1$

    }
    return string;
  }

  /**
   * Represents a collection of BON and Java types that are equivalent for our purposes.
   * @author evka
   *
   */
  public class Mapping implements Comparable < Mapping > {
    /**
     * Set of BON types as strings.
     */
    private final List < String > my_bon_types;

    /**
     * Set of Java types as strings.
     */
    private final List < String > my_java_types;

    /**
     * Name of the mapping, for easier identification.
     */
    private final String my_name;

    /**
     * Create a mapping.
     * @param a_name name of mapping
     * @param the_bon_types Bon types of mapping
     * @param the_java_types Java types of mapping
     */
    public Mapping(final String a_name, final String[] the_bon_types,
                   final String[] the_java_types) {
      this.my_name = a_name;
      my_bon_types = new Vector < String > ();
      my_java_types = new Vector < String > ();

      for (final String s : the_bon_types) {
        final String temp = s.trim().replaceAll("[,;]", ""); //$NON-NLS-1$ //$NON-NLS-2$
        if (temp.length() > 0) {
          if (!my_bon_types.contains(temp)) {
            my_bon_types.add(temp);
          }
        }
      }

      for (final String s : the_java_types) {
        final String temp = s.trim().replaceAll("[,;]", ""); //$NON-NLS-1$ //$NON-NLS-2$
        if (temp.length() > 0) {
          if (!my_java_types.contains(temp)) {
            my_java_types.add(temp);
          }
        }
      }
    }

    /**
     * Adds BON type strings to the mapping.
     * @param the_bon_types SortedSet of BON type strings
     */
    public final void addBonTypes(final String[] the_bon_types) {
      for (final String s : the_bon_types) {
        final String temp = s.trim().replaceAll("[,;]", ""); //$NON-NLS-1$ //$NON-NLS-2$
        if (temp.length() > 0) {
          if (!my_bon_types.contains(temp)) {
            my_bon_types.add(temp);
          }
        }
      }
    }


    /**
     * Adds Java type strings to the mapping.
     * @param the_java SortedSet of Java type strings
     */
    public final void addJavaTypes(final String[] the_java) {
      for (final String s : the_java) {
        final String temp = s.trim().replaceAll("[,;]", ""); //$NON-NLS-1$ //$NON-NLS-2$
        if (temp.length() > 0) {
          if (!my_java_types.contains(temp)) {
            my_java_types.add(temp);
          }
        }
      }
    }


    /**
     * Checks if the given string is part of the BON part of the mapping.
     * @param the_searched string to look
     * @return true if the string is part of the BON part of the mapping
     */
    public final boolean hasBonType(final String the_searched) {
      return my_bon_types.contains(the_searched);
    }

    /**
     * Checks if the given string is part of the Java part of the mapping.
     * @param the_searched string to look
     * @return true if the string is part of the Java part of the mapping
     */
    public final boolean hasJavaType(final String the_searched) {
      final boolean foundSimple = my_java_types.contains(the_searched);
      if (foundSimple) {
        return true;
      }
      final int index = the_searched.lastIndexOf('.');

      if (index != -1 && index != the_searched.length()) {
        return my_java_types.contains(the_searched.substring(index + 1));
      }
      return false;
    }

    /**
     * Get the name of this mapping. Serves as unique ID.
     * @return the name
     */
    public final String getName() {
      return my_name;
    }

    /**
     * Get the Bon part of a mapping.
     * @param the_name name of mapping
     * @return mapping, if present, otherwise null
     */
    public final String getBonMapping (final String the_name) {
      if (my_bon_types.contains(the_name)) {
        if (my_java_types.size() > 0) {
          return my_java_types.get(0);
        } else {
          return "null"; //$NON-NLS-1$
        }
      } else {
        return null;
      }
    }

    /**
     * Get the Java part of a mapping.
     * @param the_name name of mapping
     * @return mapping if present, otherwise null
     */
    public final String getJavaMapping (final String the_name) {
      if (my_java_types.contains(the_name)) {
        if (my_bon_types.size() > 0) {
          return my_bon_types.get(0);
        } else {
          return "Void"; //$NON-NLS-1$
        }
      } else {
        return null;
      }
    }

    /**
     * Compares on the mapping name only.
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     * @param the_map map to compare
     * @return a negative integer, zero, or a positive integer as this object is less than,
     *          equal to, or greater than the specified object.
     */
    @Override
    public final int compareTo(final Mapping the_map) {
      if (the_map == null) {
        return 1;
      }
      return my_name.compareTo(the_map.getName());
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return String representation
     */
    @Override
    public final String toString() {
      return my_name + ": " + my_bon_types + " - " + //$NON-NLS-1$ //$NON-NLS-2$
        my_java_types + "\n"; //$NON-NLS-1$;
    }

  }
}
