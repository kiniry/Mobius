/**
 * Package for data structures.
 */
package structure;

import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Vector;

import logic.Expression.Nullity;
import utils.BConst;
import utils.Helper;
import utils.BeetlzSourceLocation;
import utils.ModifierManager.ClassModifier;
import utils.ModifierManager.ClassType;
import utils.ModifierManager.FeatureModifier;
import utils.ModifierManager.VisibilityModifier;
import utils.smart.ParametrizedSmartString;
import utils.smart.SmartString;
import utils.smart.TypeSmartString;

/**
 * A container storing all necessary information about a class.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class ClassStructure implements Comparable < ClassStructure > {
  /** Is this a BON class? default */
  private ClassType my_type;
  /** Class modifier. */
  private final SortedSet < ClassModifier > my_modifiers;
  /** Visibility. */
  private final Visibility my_visibility;
  /** Generic parameter. */
  private final List < SmartString > my_generics;
  /** Simple class name. */
  private final TypeSmartString my_simplename;
  /** Implemented interface's and super classes' names. */
  private final SortedSet < SmartString > my_interfaces;
  /*** Source location. */
  private final BeetlzSourceLocation my_sourceLoc;
  /** Features. We allow duplicate features, because Java allows overriding. */
  private final SortedSet < FeatureStructure > my_features;
  /** Constructors. */
  private final SortedSet < FeatureStructure > my_constructors;
  /** Invariants. */
  private Invariant my_invariant;
  /**  Package or cluster. */
  private final List < SmartString > my_pack;
  /** Aggregation relations. */
  private final SortedSet < SmartString > my_aggregations;
  /** Shared associations. */
  private final SortedSet < SmartString > my_sharedAssociations;
  /** Commments, indexing clause... */
  private final Comment my_comments;
  /** Nullity. */
  private Nullity my_nullity;
  /** Is this class pure.  */
  private boolean my_pure;

  /**
   * Create a fully specified class.
   * @param a_class_type class type: Bon or Java
   * @param a_modifier modifier
   * @param a_visibility visibility: protected, public, private
   * @param the_generics generic parameter
   * @param a_name name
   * @param the_interfaces interfaces
   * @param the_package package name
   * @param the_source_location source location
   */
  public /*@ pure @*/ ClassStructure(final ClassType a_class_type,
                                     final SortedSet < ClassModifier > a_modifier,
                                     final Visibility a_visibility,
                                     final List < SmartString > the_generics,
                                     final TypeSmartString a_name,
                                     final SortedSet < SmartString > the_interfaces,
                                     final List < SmartString > the_package,
                                     final BeetlzSourceLocation the_source_location) {
    //final ClassStructure enclosingClass
    my_type = a_class_type;
    my_sourceLoc = the_source_location;
    my_modifiers = a_modifier;
    my_visibility = a_visibility;
    my_generics = the_generics;
    my_simplename = a_name;
    my_interfaces = the_interfaces;
    my_features = new TreeSet < FeatureStructure > ();
    my_constructors = new TreeSet < FeatureStructure > ();
    my_invariant = null;
    my_pack = the_package;
    my_aggregations = new TreeSet < SmartString > ();
    my_sharedAssociations = new TreeSet < SmartString > ();
    my_comments = new Comment();
  }

  //**************************
  // Printing methods
  //**************************

  /**
   * String representation of qualified name.
   * @see java.lang.Object#toString()
   * @return string representation
   */
  @Override
  public final String toString() {
    return my_simplename.toQualifiedString().toString();
  }

  /**
   * Returns a pretty printed string, without invariants.
   * @see java.lang.Object#toString()
   * @return pretty string
   */
  public final /*@ pure @*/ String toStringVerbose() {
    String string = ""; //$NON-NLS-1$
    //Modifier
    string += my_visibility.getActualVisibility() + " "; //$NON-NLS-1$
    for (final ClassModifier m : my_modifiers) {
      string += m.getName() + " "; //$NON-NLS-1$
    }

    //Class type and class name
    if (my_modifiers.contains(ClassModifier.JAVA_INTERFACE)) {
      string += my_simplename;
    } else {
      string += " class " + my_simplename; //$NON-NLS-1$
    }

    //Generics
    if (my_generics != null) {
      if (my_generics.size() > 0) {
        string += "["; //$NON-NLS-1$
        for (final SmartString s : my_generics) {
          string += s + ", "; //$NON-NLS-1$
        }
        string += "]"; //$NON-NLS-1$
      }
    }
    //Interfaces
    if (my_interfaces != null) {
      if (my_interfaces.size() > 0) {
        string += " implements "; //$NON-NLS-1$
        for (final SmartString intf : my_interfaces) {
          string += intf.toString() + ", "; //$NON-NLS-1$
        }
      }
    }
    //Features/methods
    for (final FeatureStructure f : my_constructors) {
      string = string + "\n" + f.toString(); //$NON-NLS-1$
    }
    for (final FeatureStructure f : my_features) {
      string = string + "\n" + f.toString(); //$NON-NLS-1$
    }

    //associations
    if (my_sharedAssociations.size() > 0) {
      string += "\n shared associations: " + my_sharedAssociations.toString(); //$NON-NLS-1$
    }

    //associations
    if (my_aggregations.size() > 0) {
      string += "\n aggregations: " + my_aggregations.toString(); //$NON-NLS-1$
    }

    if (my_invariant != null) {
      string += "\n" + my_invariant; //$NON-NLS-1$
    }
    return string + "\n"; //$NON-NLS-1$
  }

  /**
   * Creates a full print including invariant.
   * @return pretty string
   */
  public final /*@ pure @*/ String printFullClass() {
    String string = ""; //$NON-NLS-1$

    //Modifier
    string += my_visibility.getActualVisibility() + " "; //$NON-NLS-1$
    for (final ClassModifier m : my_modifiers) {
      string += m.getName() + " "; //$NON-NLS-1$
    }

    //Class type and class name
    if (my_modifiers.contains(ClassModifier.JAVA_INTERFACE)) {
      string += my_simplename;
    } else {
      string += " class " + my_simplename; //$NON-NLS-1$
    }
    //Generics
    if (my_generics.size() > 0) {
      string += "<"; //$NON-NLS-1$
      for (final SmartString s : my_generics) {
        string += s + ", "; //$NON-NLS-1$
      }
      string += ">"; //$NON-NLS-1$
    }

    //Interfaces
    if (my_interfaces.size() > 0) {
      string += " implements " + my_interfaces + " ";   //$NON-NLS-1$ //$NON-NLS-2$
    }
    string += "{"; //$NON-NLS-1$

    //Features/methods
    for (final FeatureStructure f : my_constructors) {
      string = string + "\n" + f.printFullFeature(); //$NON-NLS-1$
    }
    for (final FeatureStructure f : my_features) {
      string = string + "\n" + f.printFullFeature(); //$NON-NLS-1$
    }

    if (my_invariant != null) {
      string += "\n" + my_invariant; //$NON-NLS-1$
    }
    string += "\n   *part of package: " + my_pack; //$NON-NLS-1$

    //SourceLocation
    string += "\n(" + my_sourceLoc.toFileAndLineString() + ")\n"; //$NON-NLS-1$ //$NON-NLS-2$
    string += "}"; //$NON-NLS-1$
    return string;
  }

  //**************************
  // Getter methods
  //**************************


  /**
   * Get Modifier.
   * @return modifier
   */
  public final /*@ pure @*/ SortedSet < ClassModifier > getModifiers() {
    return my_modifiers;
  }

  /**
   * Get this class type: bon, java or not specified.
   * @return the type
   */
  public final ClassType getType() {
    return my_type;
  }

  /**
   * Get visibility.
   * @return visibility
   */
  public final /*@ pure @*/ VisibilityModifier getVisibility() {
    return my_visibility.getSpecVisibility();
  }

  /**
   * Get visibility exports.
   * @return visibility exports
   */
  public final /*@ pure @*/ List < TypeSmartString > getExports() {
    return my_visibility.getExports();
  }

  /**
   * Get qualified (unique) name.
   * @return name
   */
  public final /*@ pure @*/ SmartString getQualifiedName() {
    return my_simplename.toQualifiedString();
  }

  /**
   * Get qualified (unique) name.
   * @return name
   */
  public final /*@ pure @*/ TypeSmartString getName() {
    return my_simplename;
  }


  /**
   * Get simple name.
   * @return full path name
   */
  public final /*@ pure @*/ String getSimpleName() {
    return my_simplename.getSimpleName();
  }

  /**
   * Get interfaces.
   * @return interfaces
   */
  public final /*@ pure @*/ SortedSet < SmartString > getInterfaces() {
    return my_interfaces;
  }

  /**
   * Get source location.
   * @return source location
   */
  public final /*@ pure @*/ BeetlzSourceLocation getSourceLocation() {
    return this.my_sourceLoc;
  }

  /**
   * Get features.
   * @return features
   */
  public final /*@ pure @*/ SortedSet < FeatureStructure > getFeatures() {
    return my_features;
  }

  /**
   * Get all constructors.
   * Returns private ones also, except for enumerated types. In that case
   * private constructors are filtered out.
   * @return constructors
   */
  public final /*@ pure @*/ SortedSet < FeatureStructure > getConstructors() {
    if (my_modifiers.contains(ClassModifier.ENUM)) {
      final SortedSet < FeatureStructure > list = new TreeSet < FeatureStructure > ();
      for (final FeatureStructure f : my_constructors) {
        if (!f.isPrivate()) {
          list.add(f);
        }
      }
      return list;
    } else {
      return my_constructors;
    }
  }

  /**
   * Get invariants.
   * @return invariant
   */
  public final /*@ pure @*/ Invariant getInvariant() {
    return my_invariant;
  }


  /**
   * Get package or cluster information.
   * @return pack
   */
  public final /*@ pure @*/ List < SmartString > getPackage() {
    return my_pack;
  }

  /**
   * Get the name of the inner most package.
   * @return name of innermost package
   */
  public final SmartString getInnermostPackage() {
    if (my_pack.size() > 0) {
      return my_pack.get(my_pack.size() - 1);
    }
    return new SmartString("defaultpackage"); //$NON-NLS-1$
  }

  /**
   * Get generic names.
   * @return generics
   */
  public final /*@ pure @*/ List < SmartString > getGenerics() {
    return my_generics;
  }

  /**
   * Get all aggregations.
   * @return set of aggregating classes
   */
  public final /*@ pure @*/ SortedSet < SmartString > getAggregations() {
    return my_aggregations;
  }

  /**
   * Get all shared associations.
   * @return set of associated classes
   */
  public final /*@ pure @*/ SortedSet < SmartString > getSharedAssociations() {
    return my_sharedAssociations;
  }

  /**
   * Get shared associations.
   * @return shared association
   */
  public final /*@ pure @*/ List < SmartString > getKnownSharedAssociations() {
    final List < SmartString > list = new Vector < SmartString > ();
    for (final SmartString s : my_sharedAssociations) {
      if (Helper.typeKnown(s)) {
        list.add(s);
      }
    }
    return list;
  }

  /**
   * Get aggregations with a known type, ie with a type that has
   * been declared in the model.
   * @return list of known aggregated types
   */
  public final /*@ pure @*/ List < SmartString > getKnownAggregations() {
    final List < SmartString > list = new Vector < SmartString > ();
    for (final SmartString s : my_aggregations) {
      if (Helper.typeKnown(s)) {
        list.add(s);
      }
    }
    return list;
  }

  /**
   * Get the comments or indexing.
   * @return comments or indexing
   */
  public final Comment getComments() {
    return my_comments;
  }

  /**
   * Get the nullity.
   * @return nullity
   */
  public final Nullity getNullity() {
    return my_nullity;
  }

  //**************************
  // Adding methods
  //**************************
  /**
   * Add a feature to the class.
   * @param the_feature feature to add
   */
  public final void addFeature(final FeatureStructure the_feature) {
    if (this.isInterface() && !the_feature.isConstant() &&
        !the_feature.isModel()) { //an interface is implicitly abstract
      the_feature.addModifier(FeatureModifier.ABSTRACT);
    }
    if (the_feature.isFinal() && the_feature.isQuery()) {
      addSharedAssociation(the_feature.getSignature().getReturnValue());
    }
    the_feature.setEnclosingClass(this);
    my_features.add(the_feature);
  }

  /**
   * Add a constructor.
   * @param the_constructor constructor to add
   */
  public final void addConstructor(final FeatureStructure the_constructor) {
    if (isPure()) {
      the_constructor.addModifier(FeatureModifier.PURE);
    }
    the_constructor.setEnclosingClass(this);
    my_constructors.add(the_constructor);
  }

  /**
   * Set the comments about this class.
   * @param an_about general comment
   * @param an_author author
   * @param the_version version
   * @param the_else everything else
   */
  public final void setComment(final List < String > an_about,
                         final String an_author,
                         final String the_version,
                         final String the_else) {
    my_comments.my_about = an_about;
    my_comments.my_author = an_author;
    my_comments.my_allElse = the_else;
    my_comments.my_version = the_version;
  }

  /**
   * Add the Java interface modifier.
   */
  public final void addInterfaceModifier() {
    my_modifiers.add(ClassModifier.JAVA_INTERFACE);
  }

  /**
   * Add the BON root modifier.
   */
  public final void addRootModifier() {
    my_modifiers.add(ClassModifier.ROOT);
  }

  /**
   * Set the class type.
   * @param a_type the type to set
   */
  public final void setClassType(final ClassType a_type) {
    this.my_type = a_type;
  }

  /**
   * Set classes to which we are visible.
   * This only affects protected, package-private classe.
   * This also affects all protected and package-private features inside the class.
   * @param some_exports exports to set
   */
  public final void setExports(final List < TypeSmartString > some_exports) {
    if (isPackagePrivate() || isProtected()) {
      my_visibility.setExports(some_exports);
    }
    for (final FeatureStructure f : my_features) {
      if (f.isProtected() || f.isPackagePrivate()) {
        f.setExports(some_exports);
      }
    }
    for (final FeatureStructure f : my_constructors) {
      if (f.isProtected() || f.isPackagePrivate()) {
        f.setExports(some_exports);
      }
    }
  }

  /**
   * Set the invariant.
   * @param an_invariant invariant to set
   */
  public final void setInvariant(final Invariant an_invariant) {
    my_invariant = an_invariant;
  }

  /**
   * Add an aggregation relation.
   * @param the_name type name
   */
  public final void addAggregation(final SmartString the_name) {
    my_aggregations.add(the_name);
  }

  /**
   * Add a shared association relation.
   * @param the_name type name
   */
  public final void addSharedAssociation(final SmartString the_name) {
    my_sharedAssociations.add(the_name);
  }

  /**
   * Set this class to be pure or not.
   * @param a_pure true if pure
   */
  public final void setPure(final boolean a_pure) {
    my_pure = a_pure;
  }

  /**
   * Set the nullity of this class.
   * @param the_nullity nullity
   */
  public final void setNullity(final Nullity the_nullity) {
    my_nullity = the_nullity;
  }

  //**************************
  // Convenience methods
  //**************************
  //No convenience methods for: STATIC, FINAL, STRICTFP,

  /**
   * Is the class abstract or deferred.
   * @return true if class is abstract
   */
  public final boolean /*@ pure @*/ isAbstract() {
    return (this.my_modifiers.contains(ClassModifier.ABSTRACT));
  }

  /**
   * Is this an java interface.
   * @return true if this is an interface
   */
  public final boolean /*@ pure @*/ isInterface() {
    return my_modifiers.contains(ClassModifier.JAVA_INTERFACE);
  }

  /**
   * Is root?
   * @return true if root
   */
  public final boolean /*@ pure @*/ isRoot() {
    if (my_interfaces.contains(new TypeSmartString(BConst.RUNNABLE)) ||
        my_interfaces.contains(new TypeSmartString(BConst.THREAD)) ||
        this.hasExactFeature(new SmartString("main")).size() != 0) { //$NON-NLS-1$
      return true;
    }
    return my_modifiers.contains(ClassModifier.ROOT);
  }

  /**
   * Is root?
   * @return true if root
   */
  public final boolean /*@ pure @*/ isPersistent() {
    if (my_interfaces.contains(new TypeSmartString(BConst.SERIALIZABLE)) ||
        my_interfaces.contains(new TypeSmartString(BConst.EXTERNALIZABLE))) {
      return true;
    }
    return my_modifiers.contains(ClassModifier.PERSISTENT);
  }

  /**
   * Is this class public.
   * @return true if class is public
   */
  public final boolean /*@ pure @*/ isPublic() {
    return my_visibility.getSpecVisibility() == VisibilityModifier.PUBLIC;
  }

  /**
   * Is this class private.
   * @return true if class is private
   */
  public final boolean /*@ pure @*/ isPrivate() {
    return my_visibility.getSpecVisibility() == VisibilityModifier.PRIVATE;
  }

  /**
   * Is this class package private.
   * @return true if class is package-private
   */
  public final boolean /*@ pure @*/ isPackagePrivate() {
    return my_visibility.getSpecVisibility() == VisibilityModifier.PACKAGE_PRIVATE;
  }

  /**
   * Is this class protected.
   * @return true if class is protected
   */
  public final boolean /*@ pure @*/ isProtected() {
    return my_visibility.getSpecVisibility() == VisibilityModifier.PROTECTED;
  }

  /**
   * Is this class restricted (BON).
   * @return true if class is Bon restricted
   */
  public final boolean /*@ pure @*/ isRestricted() {
    return my_visibility.getSpecVisibility() == VisibilityModifier.RESTRICTED;
  }

  /**
   * Is this class reused.
   * @return true if class is reused
   */
  public final boolean /*@ pure @*/ isReused() {
    return my_modifiers.contains(ClassModifier.REUSED);
  }

  /**
   * Is this class interfaced, ie all features public.
   * @return true if class is interfaced
   */
  public final boolean /*@ pure @*/ isBonInterfaced() {
    return my_modifiers.contains(ClassModifier.INTERFACED);
  }

  /**
   * Is this class generic.
   * @return true if class is generic
   */
  public final boolean /*@ pure @*/ isGeneric() {
    return my_modifiers.contains(ClassModifier.GENERIC);
  }

  /**
   * Is this class an enumerated type.
   * @return true if class is enum
   */
  public final boolean /*@ pure @*/ isEnum() {
    //either we have an enum modifier...
    if (my_modifiers.contains(ClassModifier.ENUM)) {
      return true;
    }
    //or the class is a BON class and has private enumeration:SET feature
    if (my_type == ClassType.BON) {
      for (final FeatureStructure f : my_features) {
        if (f.getSimpleName().equals("enumeration") && f.isPrivate()) { //$NON-NLS-1$
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Is this class pure.
   * @return true if class is pure
   */
  public final boolean isPure() {
    return my_pure;
  }

  /**
   * Does this class have features.
   * @return true if this class has features or constructors
   */
  public final boolean hasFeatures() {
    return my_constructors.size() + my_features.size() > 0;
  }

  /**
   * Checks if the class contains a certain accessible feature.
   * Spec-Private features are not being returned.
   * @param a_name feature name to search for
   * @return  feature, if found, otherwise an empty list
   */
  public final /*@ pure @*/ List < FeatureStructure > hasFeature(final SmartString a_name) {
    final List < FeatureStructure > list = new Vector < FeatureStructure > ();
    for (final FeatureStructure c : my_features) {
      if (!c.isPrivate() && c.getName().equalsTyped(a_name)) {
        list.add(c);
      }
    }
    return list;
  }

  /**
   * Checks if the class contains a certain feature with exactly the
   * given name. Since Java allows overloading, this will be a list.
   * To accomodate this in BON, we assume the naming convention for
   * overloading: feat, feat1, feat2, feat3 etc etc.
   * @param a_name feature name to search for
   * @return  feature, if found, otherwise null
   */
  public final /*@ pure @*/ SortedSet < FeatureStructure >
  hasExactFeature(final SmartString a_name) {
    final SortedSet < FeatureStructure > list = new TreeSet < FeatureStructure > ();
    if (this.getType() == ClassType.JAVA) {
      for (final FeatureStructure c : my_features) {
        if (!c.isPrivate() && (c.getName().equalsTyped(a_name) ||
            c.getSimpleName().equals(a_name.toString()) ||
            a_name.toString().matches(c.getSimpleName() + "[0-9]"))) { //$NON-NLS-1$
          list.add(c);
        }
      }
    } else {
      for (final FeatureStructure c : my_features) {
        if (!c.isPrivate() && (c.getName().equalsTyped(a_name) ||
            c.getSimpleName().equals(a_name.toString()) ||
            c.getSimpleName().matches(a_name + "[0-9]"))) { //$NON-NLS-1$
          list.add(c);
        }
      }
    }

    return list;
  }

  /**
   * Get all features with the specified visibility.
   * @param the_visibility the visibility that the features should have
   * @return all features with given visibility
   */
  public final List < FeatureStructure >
  getFeatureByVisibility(final VisibilityModifier the_visibility) {
    final List < FeatureStructure > list = new Vector < FeatureStructure > ();
    for (final FeatureStructure f : my_features) {
      if (f.getVisibility() == the_visibility) {
        list.add(f);
      }
    }

    return list;
  }

  /**
   * Get all constructors with the specified visibility.
   * @param the_visibility the visibility that the constructors should have
   * @return all constructors with given visibility
   */
  public final List < FeatureStructure >
  getConstructorsByVisibility(final VisibilityModifier the_visibility) {
    final List < FeatureStructure > list = new Vector < FeatureStructure > ();
    for (final FeatureStructure f : my_constructors) {
      if (f.getVisibility() == the_visibility) {
        list.add(f);
      }
    }
    return list;
  }

  /**
   * Does any of this classes features use frame conditions.
   * @return true if frame conditions are used
   */
  public final /*@ pure @*/ boolean usesAssignable() {
    if (my_type == ClassType.BON) { //look for default: nothing
      for (final FeatureStructure f : my_features) {
        for (final Spec s : f.getSpec()) {
          if (!s.defaultFrame()) {
            return true;
          }
        }
      }
    }
    return false;
  }

  /**
   * Does any feature use nullity explicitly.
   * @return true if explicit nullity declarations are used
   */
  public final /*@ pure @*/ boolean usesNullity() {
    for (final FeatureStructure f : my_features) {
      if (f.getSignature().explicitNullity()) {
        return true;
      }
    }
    return false;
  }


  /**
   * Get all feature names.
   * @return feature names, concatenated by underscore
   */
  public final /*@ pure @*/ String getFeatureNames() {
    String string = ""; //$NON-NLS-1$
    for (final FeatureStructure c : my_features) {
      string += c.getName() + "_"; //$NON-NLS-1$
    }
    return string;
  }

  /**
   * Get all accesible features, ie all not private ones.
   * @return non-private features
   */
  public final /*@ pure @*/ List < FeatureStructure > getAccessibleFeatures() {
    final List < FeatureStructure > list = new Vector < FeatureStructure > ();
    for (final FeatureStructure f : my_features) {
      if (f.getVisibility() != VisibilityModifier.PRIVATE) {
        list.add(f);
      }
    }
    return list;
  }

  /**
   * Get the compound name of this class.
   * @return compound name
   */
  public final /*@ pure @*/ SmartString getCompoundName() {
    final int two = 2;
    if (my_generics.size() == 0) {
      return my_simplename;
    } else {
      String str = my_simplename.toString() + "["; //$NON-NLS-1$
      for (final SmartString s : my_generics) {
        str += s.toString() + ", "; //$NON-NLS-1$
      }
      str = str.substring(0, str.length() - two);
      str += "]"; //$NON-NLS-1$
      final List < SmartString > list = new Vector < SmartString > (my_generics);
      return new ParametrizedSmartString(str, my_simplename, list);
    }
  }

  /**
   * Compare two classes.
   * Compare based on visibility, package containment and name, in that order.
   * @see java.lang.Comparable#compareTo(java.lang.Object)
   * @param the_other class structure
   * @return order of classes
   */
  @Override
  public final int /*@ pure @*/ compareTo(final ClassStructure the_other) {
    if (the_other == null) {
      return 1;
    }

    if (my_visibility.getSpecVisibility() != the_other.my_visibility.getSpecVisibility()) {
      return my_visibility.getSpecVisibility().
        compareTo(the_other.my_visibility.getSpecVisibility());
    }
    if (my_visibility.getActualVisibility() != the_other.my_visibility.getActualVisibility()) {
      return my_visibility.getActualVisibility().
        compareTo(the_other.my_visibility.getActualVisibility());
    }
    if (my_simplename.toString().compareTo(the_other.my_simplename.toString()) != 0) {
      return my_simplename.toString().compareTo(the_other.my_simplename.toString());
    }
    return 0;

  }


  /**
   * Container class holding comment lines.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public class Comment {
    /** Author comment. */
    public String my_author;
    /** General description. */
    public List < String > my_about;
    /** Version comment. */
    public String my_version;
    /** All other comments. */
    public String my_allElse;

    /**
     * Is this comment empty.
     * @return true if all parts are empty
     */
    public final boolean isEmpty() {
      return (my_about == null || my_about.isEmpty()) &&
        (my_author == null || my_author.length() == 0) &&
        (my_version == null || my_version.length() == 0) &&
        (my_allElse == null || my_allElse.length() == 0);

    }
  }

}
