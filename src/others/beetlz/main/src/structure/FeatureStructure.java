/**
 * Package for data structures.
 */
package structure;

import java.util.HashMap;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Vector;

import main.Beetlz;
import utils.FeatureType;
import utils.SourceLocation;
import utils.ModifierManager.FeatureModifier;
import utils.ModifierManager.VisibilityModifier;
import utils.smart.FeatureSmartString;
import utils.smart.SmartString;
import utils.smart.TypeSmartString;

/**
 * Container class for Java methods and public fields and BON features.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class FeatureStructure implements Comparable < FeatureStructure > {
  /** Modifier. */
  private final SortedSet < FeatureModifier > my_modifiers;
  /** Visibility modifier. */
  private final Visibility my_visibility;
  /** Feature name. */
  private final FeatureSmartString my_name;
  /** Generic parameter. */
  private List < SmartString > my_generics;
  /** Signature. */
  private final Signature my_signature;
  /** Pre- postconditions and frame constraints. */
  private List < Spec > my_spec;
  /** Source location. */
  private final SourceLocation my_sourceLoc;
  /** Comments.  */
  private String my_comment;
  /** Renaming. */
  private Renaming my_renaming;
  /** Enclosing class. */
  private ClassStructure my_enclosingClass;

  /**
   * Create a fully specified feature.
   * @param a_modifier modifier
   * @param a_visibility visibility
   * @param a_name feature name
   * @param a_signature signature
   * @param a_spec specification
   * @param a_source_location sourcelocation
   * @param a_renaming_class renaming class
   * @param a_renaming_feature renaming feature
   * @param a_enclosing_class enclosing class
   */
  public /*@ pure @*/ FeatureStructure(final SortedSet < FeatureModifier > a_modifier,
                                       final Visibility a_visibility,
                                       final FeatureSmartString a_name,
                                       final Signature a_signature,
                                       final List < Spec > a_spec,
                                       final SourceLocation a_source_location,
                                       final /*@ nullable @*/ String a_renaming_class,
                                       final /*@ nullable @*/ String a_renaming_feature,
                                       final ClassStructure a_enclosing_class) {
    my_modifiers = a_modifier;
    my_visibility = a_visibility;
    my_name = a_name;
    my_signature = a_signature;
    my_spec = a_spec;
    my_sourceLoc = a_source_location;
    if (a_renaming_class != null && a_renaming_feature != null) {
      my_renaming = new Renaming(a_renaming_class, a_renaming_feature);
    } else {
      my_renaming = null;
    }
    my_generics = new Vector < SmartString > ();
    my_enclosingClass = a_enclosing_class;
  }

  /**
   * Create a default feature.
   * Default settings are: public, UNKNOWN_NAME, void return type and no arguments.
   */
  public /*@ pure @*/ FeatureStructure() {
    my_modifiers = new TreeSet < FeatureModifier > ();
    my_visibility = new Visibility(VisibilityModifier.PUBLIC);
    my_name = new FeatureSmartString("UNKNOWN_NAME"); //$NON-NLS-1$
    my_signature = new Signature(SmartString.getVoid(),
                                 new HashMap < String , SmartString > ());
    my_spec = new Vector < Spec > ();
    my_sourceLoc = new SourceLocation();
    my_renaming = null;
    my_enclosingClass = new ClassStructure();
    my_generics = new Vector < SmartString > ();
  }

  //**************************
  // Printing methods
  //**************************
  /**
   * Print a short string.
   * @return string representation
   */
  public final String toShortString() {
    String string = "    "; //$NON-NLS-1$
    //Modifier
    string += my_visibility.getActualVisibility() + " "; //$NON-NLS-1$

    for (final FeatureModifier m : my_modifiers) {
      string += m.getName() + " "; //$NON-NLS-1$
    }

    string += " " + my_signature.getReturnValue(); //$NON-NLS-1$
    string += " " + my_name + " " + "("; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
    for (final SmartString arg : my_signature.getFormalTypes()) {
      string = string + arg + ", "; //$NON-NLS-1$
    }
    string += ")"; //$NON-NLS-1$

    return string;
  }

  /**
   * Get a pretty printed string.
   * @see java.lang.Object#toString()
   * @return pretty string
   */
  @Override
  public final /*@ pure @*/ String toString() {
    String string = "    "; //$NON-NLS-1$
    //Modifier
    if (my_visibility.getSpecVisibility() != my_visibility.getActualVisibility()) {
      string += my_visibility.getSpecVisibility() + "( " +  //$NON-NLS-1$
        my_visibility.getActualVisibility() + " ) "; //$NON-NLS-1$
    } else {
      string += my_visibility.getActualVisibility() + " "; //$NON-NLS-1$
    }
    for (final FeatureModifier m : my_modifiers) {
      string += m.getName() + " "; //$NON-NLS-1$
    }

    string += " " + my_signature.getReturnValue() +  //$NON-NLS-1$
      "(" + my_signature.getReturnValue().getNullity() + ")"; //$NON-NLS-1$ //$NON-NLS-2$
    string += " " + my_name + " " + "("; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
    for (final SmartString arg : my_signature.getFormalTypes()) {
      string = string + arg +
        "(" + arg.getNullity() + ")" + ", "; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
    }

    string = string + ");"; //$NON-NLS-1$
    if (my_visibility.getExports().size() > 0) {
      string += "\n\texports: " + my_visibility.getExports(); //$NON-NLS-1$
    }
    if (!my_spec.isEmpty()) {
      string += "\n\tspec: " + my_spec.toString(); //$NON-NLS-1$
    }

    return string;
  }

  /**
   * Get a pretty printed string with the full signature including pre and postconditions.
   * @return pretty string
   */
  public final /*@ pure @*/ String printFullFeature() {
    String string = "    "; //$NON-NLS-1$

    //Modifier
    if (my_visibility.getSpecVisibility() != my_visibility.getActualVisibility()) {
      string += my_visibility.getSpecVisibility() + "( " +  //$NON-NLS-1$
        my_visibility.getActualVisibility() + " ) "; //$NON-NLS-1$
    } else {
      string += my_visibility.getActualVisibility() + " "; //$NON-NLS-1$
    }
    for (final FeatureModifier m : my_modifiers) {
      string += m.getName() + " "; //$NON-NLS-1$
    }
    string += " " + my_signature.getReturnValue(); //$NON-NLS-1$
    string += " " + my_name + " " + "("; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
    for (final SmartString arg : my_signature.getFormalTypes()) {
      string = string + arg + ", "; //$NON-NLS-1$
    }

    string = string + ");"; //$NON-NLS-1$
    string += "\n" + my_spec.toString(); //$NON-NLS-1$

    if (my_renaming != null) {
      string += "\n       *renamed: " +
        my_renaming.getClassName() + "." + //$NON-NLS-1$ //$NON-NLS-2$
        my_renaming.getFeatureName();
    }
    if (my_visibility.getExports().size() > 0) {
      string += "\n       *exports: " + my_visibility.getExports(); //$NON-NLS-1$
    }
    //SourceLocation
    string += "\n       *" + my_sourceLoc.toString() + "\n"; //$NON-NLS-1$ //$NON-NLS-2$
    return string;
  }

  //**************************
  // Getter methods
  //**************************

  /**
   * Get modifier.
   * @return modifier
   */
  public final /*@ pure @*/ SortedSet < FeatureModifier > getModifiers() {
    return my_modifiers;
  }

  /**
   * Get specification related visibility.
   * Hence for Java methods, if specified as spec-public or spec-protected,
   * otherwise the actual API visibility.
   * @return visibility
   */
  public final /*@ pure @*/ VisibilityModifier getVisibility() {
    return my_visibility.getSpecVisibility();
  }

  /**
   * Get feature name.
   * @return feature name
   */
  public final /*@ pure @*/ SmartString getName() {
    return my_name;
  }

  /**
   * Get a simple name.
   * @return simple name
   */
  public final /*@ pure @*/ String getSimpleName() {
    return my_name.toString();
  }

  /**
   * Get return value.
   * @return return value
   */
  public final /*@ pure @*/ Signature getSignature() {
    return my_signature;
  }


  /**
   * Get specification.
   * @return specs
   */
  public final /*@ pure @*/ List < Spec > getSpec() {
    return my_spec;
  }




  /**
   * Get source location.
   * @return source location
   */
  public final /*@ pure @*/ SourceLocation getSourceLoc() {
    return my_sourceLoc;
  }

  /**
   * Get comments.
   * @return comments
   */
  public final /*@ pure @*/ String getComment() {
    return my_comment;
  }

  /**
   * Get renaming.
   * @return renaming
   */
  public final /*@ pure @*/ Renaming getRenaming() {
    return my_renaming;
  }

  /**
   * Get feature type.
   * @return feature type
   */
  public final /*@ pure @*/ FeatureType getFeatureType() {
    if (my_spec.isEmpty()) {
      return FeatureType.UNKNOWN;
    }
    return my_spec.get(0).getFeatureType();
  }

  /**
   * Get exports.
   * @return exports
   */
  public final /*@ pure @*/ List < TypeSmartString > getExports() {
    return my_visibility.getExports();
  }

  /**
   * Get enclosing class.
   * @return enclosing class
   */
  public final /*@ pure @*/ ClassStructure getEnclosingClass() {
    return my_enclosingClass;
  }

  /**
   * Get generics.
   * @return generics
   */
  public final List < SmartString > getGenerics() {
    return my_generics;
  }

  /**
   * Set enclosing class.
   * @param a_class new enclosing class
   */
  protected final void setEnclosingClass(final ClassStructure a_class) {
    this.my_enclosingClass = a_class;
  }

  /**
   * Add another modifier.
   * @param a_modifier new modifier
   */
  protected final void addModifier(final FeatureModifier a_modifier) {
    my_modifiers.add(a_modifier);
  }

  /**
   * Set the specification.
   * @param some_specs specs to set
   */
  public final void setSpecs(final List < Spec > some_specs) {
    my_spec = some_specs;
  }

  /**
   * Does this feature equals the other.
   * @see java.lang.Object#equals(java.lang.Object)
   * @param some_obj object to compare to
   * @return true if they are equal
   */
  @Override
  public final boolean equals(final Object some_obj) {
    //keep the default
    if (this == some_obj) {
      return true;
    }
    if (getClass() != some_obj.getClass()) {
      return false;
    }

    //if we have null in either one, no comparison makes sense
    if (some_obj == null) {
      return false;
    }

    if (this.compareTo((FeatureStructure)some_obj) == 0) {
      return true;
    }
    return false;
  }


  /**
   * Compare to another feature.
   * Comparison based on visibility, feature type, name and parameter number, in this order.
   * @see java.lang.Comparable#compareTo(java.lang.Object)
   * @param the_other feature to compare to
   * @return order
   */
  public final /*@ pure @*/ int compareTo(final FeatureStructure the_other) {
    if (the_other == null) {
      return 1;
    }
    if (!my_spec.isEmpty() && !the_other.my_spec.isEmpty()) {
      if (my_spec.get(0).getFeatureType() != the_other.my_spec.get(0).getFeatureType()) {
        return my_spec.get(0).getFeatureType().
        compareTo(the_other.my_spec.get(0).getFeatureType());
      }
    }
    if (my_visibility.getSpecVisibility() != the_other.my_visibility.getSpecVisibility()) {
      return my_visibility.getSpecVisibility().
        compareTo(the_other.my_visibility.getSpecVisibility());
    }

    if (!this.my_name.equals(the_other.my_name)) {
      return this.my_name.compareTo(the_other.my_name);
    }
    if (my_signature.getFormalParameter().size() !=
      the_other.getSignature().getFormalParameter().size()) {
      if (my_signature.getFormalParameter().size() <
          the_other.getSignature().getFormalParameter().size()) {
        return -1;
      } else {
        return 1;
      }
    }
    for (int i = 0; i < my_signature.getFormalParameter().size(); i++) {
      if (my_signature.getFormalTypes().get(i).
          compareTo(the_other.getSignature().getFormalTypes().get(i)) != 0) {
        return my_signature.getFormalTypes().get(i).
        compareTo(the_other.getSignature().getFormalTypes().get(i));
      }
    }
    return 0;
  }



  //**************************
  // Setter methods
  //**************************

  /**
   * Set renaming.
   * @param the_renaming the renaming to set
   */
  public final void setRenaming(final Renaming the_renaming) {
    this.my_renaming = the_renaming;
  }

  /**
   * Set the exports.
   * @param some_exports list of types allowed access
   */
  public final void setExports(final List < TypeSmartString > some_exports) {
    my_visibility.setExports(some_exports);
  }

  /**
   * Set comment.
   * @param the_comment the comment to set
   */
  public final void setComment(final String the_comment) {
    this.my_comment = the_comment;
  }

  /**
   * Set the generics.
   * @param the_generics generic parameters
   */
  public final void setGenerics(final List < SmartString > the_generics) {
    my_generics = the_generics;
  }

  /**
   * Add comment.
   * @param the_comment comments
   */
  public final void addComment(final String the_comment) {
    this.my_comment += "\n" + the_comment; //$NON-NLS-1$
  }

  //**************************
  // member classes
  //**************************
  /**
   * Container class for renaming clause.
   */
  public class Renaming {
    /**
     * Old class name.
     */
    private final SmartString my_className;
    /**
     * Old feature name.
     */
    private final SmartString my_featureName;

    /**
     * Create a new renaming.
     * @param a_class_name old class name
     * @param a_feature_name old feature name
     */
    public /*@ pure @*/ Renaming(final String a_class_name,
                                 final String a_feature_name) {
      this.my_className = new SmartString(a_class_name);
      this.my_featureName = new SmartString(a_feature_name);
    }

    /**
     * Get old class name.
     * @return the className
     */
    public final /*@ pure @*/ SmartString getClassName() {
      return my_className;
    }

    /**
     * Get old feature name.
     * @return the featureName
     */
    public final /*@ pure @*/ SmartString getFeatureName() {
      return my_featureName;
    }

  }

  //**************************
  // Convenience methods
  //**************************

  /**
   * Is this feature public.
   * @return true if feature is public
   */
  public final boolean /*@ pure @*/ isPublic() {
    if (Beetlz.getProfile().noJml()) {
      return my_visibility.getActualVisibility() == VisibilityModifier.PUBLIC;
    }
    return my_visibility.getSpecVisibility() == VisibilityModifier.PUBLIC;
  }

  /**
   * Is this feature public.
   * @return true if feature is public
   */
  public final boolean /*@ pure @*/ isProtected() {
    if (Beetlz.getProfile().noJml()) {
      return my_visibility.getActualVisibility() == VisibilityModifier.PROTECTED;
    }
    return my_visibility.getSpecVisibility() == VisibilityModifier.PROTECTED;
  }

  /**
   * Is this feature public.
   * @return true if feature is public
   */
  public final boolean /*@ pure @*/ isPackagePrivate() {
    if (Beetlz.getProfile().noJml()) {
      return my_visibility.getActualVisibility() == VisibilityModifier.PACKAGE_PRIVATE;
    }
    return my_visibility.getSpecVisibility() == VisibilityModifier.PACKAGE_PRIVATE;
  }

  /**
   * Is this feature public.
   * @return true if feature is public
   */
  public final boolean /*@ pure @*/ isRestricted() {
    return my_visibility.getSpecVisibility() == VisibilityModifier.RESTRICTED;
  }

  /**
   * Is this feature public.
   * @return true if feature is public
   */
  public final boolean /*@ pure @*/ isPrivate() {
    if (Beetlz.getProfile().noJml()) {
      return my_visibility.getActualVisibility() == VisibilityModifier.PRIVATE;
    }
    return my_visibility.getSpecVisibility() == VisibilityModifier.PRIVATE;
  }

  /**
   * Is this feature abstract.
   * @return true if feature is abstract
   */
  public final boolean /*@ pure @*/ isAbstract() {
    return (my_modifiers.contains(FeatureModifier.ABSTRACT));
    //|| my_modifiers.contains(FeatureModifier.DEFERRED));
  }

  /**
   * Is this feature constant.
   * @return true if feature is constant
   */
  public final boolean /*@ pure @*/ isConstant() {
    if (my_spec.isEmpty()) {
      return false;
    }
    return my_spec.get(0).isConstant();
  }

  /**
   * Is this feature redefined.
   * @return true if feature is redefined
   */
  public final boolean /*@ pure @*/ isRedefined() {
    return my_modifiers.contains(FeatureModifier.REDEFINED);
  }

  /**
   * Is this feature final.
   * @return true is the feature has a final modifier
   */
  public final boolean /*@ pure @*/ isFinal() {
    return my_modifiers.contains(FeatureModifier.FINAL);
  }

  /**
   * Is this feature a query.
   * @return true if it is a query
   */
  public final boolean /*@ pure @*/ isQuery() {
    if (my_spec.isEmpty()) {
      return false;
    }
    return my_spec.get(0).getFeatureType() == FeatureType.QUERY;
  }

  /**
   * Is this feature a command.
   * @return true if it is a command
   */
  public final boolean /*@ pure @*/ isCommand() {
    if (my_spec.isEmpty()) {
      return false;
    }
    return my_spec.get(0).getFeatureType() == FeatureType.COMMAND;
  }

  /**
   * Is this a model method or field.
   * @return true is it has a model modifier
   */
  public final boolean isModel() {
    return my_modifiers.contains(FeatureModifier.MODEL);
  }

  /**
   * Is this feature a ghost.
   * @return true if it has a ghost modifier
   */
  public final boolean isGhost() {
    return my_modifiers.contains(FeatureModifier.GHOST);
  }
}
