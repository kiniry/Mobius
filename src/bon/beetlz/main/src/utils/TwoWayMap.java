/**
 * Package with utility classes.
 */
package utils;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import main.Beetlz;

/**
 * A bidirectional map.
 * Java does not have one.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 * @param <T> first type of mapping
 * @param <S> second type of mapping
 */
public class TwoWayMap < T, S > {
  /** < BON, Java >. */
  private final Map < T, S > my_bonKeys;
  /** < Java, BON > . */
  private final Map < S, T > my_javaKeys;

  /**
   * Create a new two-way map.
   */
  public TwoWayMap() {
    my_bonKeys = new HashMap < T, S > ();
    my_javaKeys = new HashMap < S, T > ();
  }

  /**
   * Checks whether a BON key is present.
   * @param a_bon_name key to search for
   * @return true if key is present
   */
  public final boolean containsBonKey(final T a_bon_name) {
    return my_bonKeys.containsKey(a_bon_name);
  }

  /**
   * Checks whether a Java key is present.
   * @param a_java_name key to search for
   * @return true is key is present
   */
  public final boolean containsJavaKey(final S a_java_name) {
    return my_javaKeys.containsKey(a_java_name);
  }

  /**
   * Get all BON entries.
   * @return set of all entries
   */
  public final Set < T > bonEntries() {
    return my_bonKeys.keySet();
  }

  /**
   * Get all Java entries.
   * @return set of all entries
   */
  public final Set < S > javaEntries() {
    return my_javaKeys.keySet();
  }

  /**
   * Get an entry of a key.
   * @param a_name key
   * @return null if not in map
   */
  public final Object get(final Object a_name) {
    if (my_bonKeys.containsKey(a_name)) {
      return my_bonKeys.get(a_name);
    } else if (my_javaKeys.containsKey(a_name)) {
      return my_javaKeys.get(a_name);
    } else {
      return null;
    }
  }

  /**
   * Is map is empty.
   * @return true if map is empty
   */
  public final boolean isEmpty() {
    return (my_bonKeys.size() == 0);
  }


  /**
   * Returns -1 if mapping already exists.
   * @param a_bon_name BON key
   * @param a_java_name Java key
   * @return true if keys have been added, if keys are already present,
   * returns false
   */
  public final boolean put(final T a_bon_name, final S a_java_name) {
    if (my_bonKeys.containsKey(a_bon_name) || my_javaKeys.containsKey(a_java_name)) {
      return false;
    }
    my_bonKeys.put(a_bon_name, a_java_name);
    my_javaKeys.put(a_java_name, a_bon_name);

    //get position in maps
    return true;
  }

  /**
   * Size of this map.
   * @return size of map
   */
  public final int size() {
    return my_bonKeys.size();
  }

  /**
   * String representation.
   * @see java.lang.Object#toString()
   * @return string with contents
   */
  @Override
  public final String toString() {
    String string = "two-way-map: \n"; //$NON-NLS-1$
    string += my_bonKeys.toString() + "\n" + my_javaKeys.toString(); //$NON-NLS-1$
    return string;
  }

}
