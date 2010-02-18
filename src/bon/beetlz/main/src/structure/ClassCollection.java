/**
 * Package for data structures.
 */
package structure;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import utils.smart.SmartString;
import utils.smart.TypeSmartString;
import utils.smart.TypeSmartStringWithLocation;

/**
 * A collection of parsed classes in a system.
 * The classes are unique and identified by name.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class ClassCollection {

  /**
   * Holds the classes in one structure, sorted by class name.
   * They are identified by their name. Since Java allows the same
   * name in different packages, we use qualified names.
   */
  private final /*@ spec-public @*/ Map < TypeSmartString, ClassStructure > my_classes;
  /** Classes sorted by packages. */
  private final Map < SmartString, List < ClassStructure > > my_packages;

  /**
   * Creates a new empty collection.
   */
  public ClassCollection() {
    my_classes = new HashMap < TypeSmartString, ClassStructure > ();
    my_packages = new HashMap < SmartString, List < ClassStructure > > ();
  }


  /**
   * Add several classes at once.
   * Also maintains a secodn list with classes sorted by package they belong to.
   * @param the_classes a map of the new classes.
   */
  public final void addMoreClasses(final Map < String, ClassStructure > the_classes) {
    for (final ClassStructure cls : the_classes.values()) {
      final SmartString p = cls.getInnermostPackage();
      my_classes.put(cls.getName(), cls);
      if (my_packages.containsKey(p)) {
        my_packages.get(p).add(cls);
      } else {
        final List < ClassStructure > newList = new Vector < ClassStructure > ();
        newList.add(cls);
        my_packages.put(p, newList);
      }
    }

  }

  /**
   * Add a class to this collection.
   * @param a_class class to be added
   */
  public final void addClass(final ClassStructure a_class) {
    my_classes.put(a_class.getName(), a_class);
    final SmartString p = a_class.getInnermostPackage();
    if (my_packages.containsKey(p)) {
      my_packages.get(p).add(a_class);
    } else {
      final List < ClassStructure > newList = new Vector < ClassStructure > ();
      newList.add(a_class);
      my_packages.put(p, newList);
    }
  }

  /**
   * Returns the contained classes.
   * @return contained classes
   */
  public final /*@ pure @*/ Collection < ClassStructure > getClasses() {
    return my_classes.values();
  }

  /**
   * Get a class by qualified name.
   * @param a_name qualified name of class to be found
   * @return null if not found
   */
  public final /*@ pure @*/ ClassStructure getClass(final String a_name) {
    return my_classes.get(new TypeSmartString(a_name));

  }

  /**
   * Gives number of classes in the collection.
   * @return number of classes
   */
  public final /*@ pure @*/ int getNumberClasses() {
    return my_classes.size();
  }

  /**
   * Returns all keys, ie class names.
   * @return list of keys
   */
  public final /*@ pure @ */ List < TypeSmartStringWithLocation > getAccesibleClassTypes() {
    final List < TypeSmartStringWithLocation > list = new ArrayList < TypeSmartStringWithLocation > ();
    for (final ClassStructure cls : my_classes.values()) {
      if (!cls.isPrivate()) {
        list.add(new TypeSmartStringWithLocation(cls.getName(), cls.getSourceLocation()));
      }
    }
    return list;
  }
  
  public final /*@ pure @ */ List < TypeSmartString > getAccesibleClassTypesNoLoc() {
    final List < TypeSmartString > list = new ArrayList < TypeSmartString > ();
    for (final ClassStructure cls : my_classes.values()) {
      if (!cls.isPrivate()) {
        list.add(cls.getName());
      }
    }
    return list;
  }
  
  /**
   * Returns a pretty printed string.
   * @see java.lang.Object#toString()
   * @return pretty printed string
   */
  @Override
  public final /*@ pure @*/ String toString() {
    return getAccesibleClassTypes().toString();
  }

}
