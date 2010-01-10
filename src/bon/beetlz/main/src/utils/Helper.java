/**
 * Package for utility classes.
 */
package utils;

import java.util.Collection;
import java.util.List;

import logic.BeetlzExpression;
import main.Beetlz;

import structure.ClassStructure;
import structure.FeatureStructure;
import utils.smart.FeatureSmartString;
import utils.smart.GenericParameter;
import utils.smart.TypeSmartString;
import utils.smart.SmartString;

/**
 * Helper methods used in several places.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public final class Helper {

  /**
   * Make this class not instanciable.
   */
  private Helper () { }

  /**
   * A class qualifies as an interface if all features are deferred and public,
   * or are constant queries.
   * @param a_class class to be checked
   * @return true of class can be a Java interface
   */
  public static boolean qualifiesAsInterface(final ClassStructure a_class) {
    if (a_class.isInterface()) {
      return true;
    }

    if (a_class.getFeatures().size() == 0) { //no features, then only check deferred
      return a_class.isAbstract();
    }

    for (final FeatureStructure f : a_class.getFeatures()) {
      if (f.isConstant()) {
        continue;
      }
      if (!f.isModel() && (!f.isAbstract() || !f.isPublic())) {
        //model fields do not count into this
        return false;
      }
    }
    return true;
  }


  /**
   * Interfaced does not or should not apply to classes without any features.
   * @param a_class class to check
   * @return true if can be qualified as BON interfaced
   */
  public static boolean qualifiesAsBonInterfaced(final ClassStructure a_class) {
    if (!a_class.hasFeatures() && a_class.getConstructors().size() == 0) {
      return false;
    }
    for (final FeatureStructure f : a_class.getFeatures()) {
      if (!f.isPublic()) return false;
    }
    for (final FeatureStructure f : a_class.getConstructors()) {
      if (!f.isPublic()) return false;
    }
    return true;
  }

  /**
   * Test if a feature is an accessor.
   * This is true, if there exists another feature by the same
   * name minus get-, has-, or is- prefixes.
   * @param the_class class where feature belongs to
   * @param the_feature feature to check
   * @return true if feature is an accessor by this test
   */
  public static boolean testIsAccessor(final ClassStructure the_class,
                                       final FeatureStructure the_feature) {
    final String name = the_feature.getSimpleName();
    final int two = 2;
    final int three = 3;
    if (name.startsWith(BConst.METHOD_GET) || name.startsWith(BConst.METHOD_HAS)) {
      if (the_class.
          hasExactFeature(new FeatureSmartString(name.
                                                 substring(three))).
                                                 size() > 0) {
        return true;
      }
    }
    if (name.startsWith(BConst.METHOD_IS)) {
      if (the_class.hasExactFeature(new FeatureSmartString(name.substring(two))).size() > 0) {
        return true;
      }
    }
    return false;
  }


  /**
   * Is this type known.
   * By known we mean whether this type has been declared in this model.
   * @param the_type type to check
   * @return true if type is known in this model
   */
  public static boolean typeKnown(final SmartString the_type) {
    for (final String t : Beetlz.getClassMap().bonEntries()) {
      if (the_type.compareToTyped(new TypeSmartString(t)) == 0) {
        return true;
      }
    }
    for (final String t : Beetlz.getClassMap().javaEntries()) {
      if (the_type.compareToTyped(new TypeSmartString(t)) == 0) {
        return true;
      }
    }

    return false;
  }

  /**
   * Helper method to check if a SmartString is present in a collection.
   * We need a separate method because we are not using the normal
   * equals method.
   * @param a_collection collection to be checked
   * @param a_type type to check for presents
   * @return true if smart string is present
   */
  public static boolean containsTyped(final Collection < SmartString > a_collection,
                                            final SmartString a_type) {
    for (final SmartString s : a_collection) {
      if (s.compareToTyped(a_type) == 0) {
        return true;
      }
    }
    return false;
  }

  /**
   * Helper method to check if a FeatureSmartString is present in a collection.
   * We need a separate method because we are not using the normal
   * equals method.
   * @param a_coll collection to be checked
   * @param a_type type to check for presents
   * @return true if smart string is present
   */
  public static boolean containsTyped(final Collection < FeatureSmartString > a_coll,
                                            final FeatureSmartString a_type) {
    for (final FeatureSmartString s : a_coll) {
      if (s.compareToTyped(a_type) == 0) {
        return true;
      }
    }
    return false;
  }
  
  public static boolean containsTyped(final Collection < BeetlzExpression > a_coll,
      final BeetlzExpression a_type) {
    for (final BeetlzExpression s : a_coll) {
      if (s.compareToTyped(a_type) == 0) {
        return true;
      }
    }
    return false;
  }

  /**
   * Checks whether the string is a generics dummy parameter.
   * @param the_string string to check
   * @param the_feature feature
   * @return true if this is a generics dummy
   */
  public static boolean isGenericsDummy(final String the_string,
                                              final FeatureStructure the_feature) {
    final List < SmartString > gen = the_feature.getEnclosingClass().getGenerics();
    for (final SmartString s : gen) {
      if (s instanceof GenericParameter) {
        if (((GenericParameter)s).getDummyName().equals(the_string)) {
          return true;
        }
      }
    }
    return false;
  }
}
