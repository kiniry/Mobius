/**
 * Package for data structures.
 */
package structure;

import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Vector;

import logic.Expression;
import utils.FeatureType;
import utils.ModifierManager.ClassType;
import utils.smart.FeatureSmartString;

/**
 * Container class for feature/method specification.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class Spec {
  /** Unknown value. */
  public static final String UNKNOWN_VALUE = "constant value"; //$NON-NLS-1$
  /** The type is needed since some defaults are different for BON or Java. */
  private final ClassType my_type;
  /** Precondition. */
  private final List < Expression > my_precondition;
  /** Postcondition.  */
  private final List < Expression > my_postcondition;
  /** Frame condition. */
  private final SortedSet < FeatureSmartString > my_frame;
  /** A constant value if the feature/method is constant. */
  private final /*@ nullable @*/ String my_constantValue;
  /** Feature type: field, query, command, mixed, unknown. */
  private final FeatureType my_featureType;


  /**
   * Dummy specs.
   */
  public Spec() {
    my_precondition = new Vector < Expression > ();
    my_postcondition = new Vector < Expression > ();
    my_frame = new TreeSet < FeatureSmartString > ();
    my_constantValue = null;
    my_featureType = FeatureType.UNKNOWN;
    my_type = ClassType.NOT_SPECIFIED;
  }

  /**
   * Create a new specification.
   * @param a_pre preconditions
   * @param a_post postconditions
   * @param a_frame frame conditions
   * @param a_const constant value, if applicable
   * @param a_type feature type (query or command)
   * @param a_clstype class type
   */
  public Spec(final List < Expression > a_pre,
              final List < Expression > a_post,
              final SortedSet < FeatureSmartString > a_frame,
              /*@ nullable @*/ final String a_const,
              final FeatureType a_type,
              final ClassType a_clstype) {
    my_precondition = a_pre;
    my_postcondition = a_post;
    my_frame = a_frame;
    my_constantValue = a_const;
    my_featureType = a_type;
    my_type = a_clstype;
  }


  /**
   * Get all preconditions.
   * @return the preconditions
   */
  public final List < Expression > getPreconditions() {
    return my_precondition;
  }

  /**
   * Get all non informal preconditions.
   * @return non informal preconditions
   */
  public final List < Expression > getNonTrivialPreconditions() {
    final List < Expression > list = new Vector < Expression > ();
    for (final Expression e : my_precondition) {
      if (!e.skip()) {
        list.add(e);
      }
    }
    return list;
  }

  /**
   * Get informal preconditions.
   * @return all informal preconditions
   */
  public final List < Expression > getInformalPreconditions() {
    final List < Expression > list = new Vector < Expression > ();
    for (final Expression e : my_precondition) {
      if (e.skip()) {
        list.add(e);
      }
    }
    return list;
  }

  /**
   * Get non informal postconditions.
   * @return non informal postconditions
   */
  public final List < Expression > getNonTrivialPostconditions() {
    final List < Expression > list = new Vector < Expression > ();
    for (final Expression e : my_postcondition) {
      if (!e.skip()) {
        list.add(e);
      }
    }
    return list;
  }

  /**
   * Get informal postconditions.
   * @return informal postconditions
   */
  public final List < Expression > getInformalPostconditions() {
    final List < Expression > list = new Vector < Expression > ();
    for (final Expression e : my_postcondition) {
      if (e.skip()) {
        list.add(e);
      }
    }
    return list;
  }

  /**
   * Get all postconditions.
   * @return the postcondition
   */
  public final List < Expression > getPostconditions() {
    return my_postcondition;
  }

  /**
   * Get frame conditions.
   * @return the frame
   */
  public final SortedSet < FeatureSmartString > getFrame() {
    return my_frame;
  }

  /**
   * Get the constant value.
   * @return the constant value
   */
  public final String getConstantValue() {
    return my_constantValue;
  }

  /**
   * Get the feature type.
   * @return the constant value
   */
  public final FeatureType getFeatureType() {
    return my_featureType;
  }

  /**
   * Is this feature constant.
   * @return true if constant value is present
   */
  public final boolean isConstant() {
    return my_constantValue != null;
  }

  /**
   * Does this feature have a default frame.
   * @return true is default frame
   */
  public final boolean defaultFrame() {
    if (my_type == ClassType.BON) {
      return my_frame.size() == 1 &&
      my_frame.first().equals(FeatureSmartString.nothing());
    } else if (my_type == ClassType.JAVA) {
      return my_frame.size() == 1 &&
      my_frame.first().equals(FeatureSmartString.everything());
    } else {
      return false;
    }
  }

  /**
   * Is the frame one of the keywords.
   * @return true if keyword is used
   */
  public final boolean frameIsKeyword() {
    if (my_frame.size() == 1) {
      if (my_frame.first().equals(FeatureSmartString.everything()) ||
          my_frame.first().equals(FeatureSmartString.nothing())) {
        return true;
      }
    }
    return false;
  }

  /**
   * String representation.
   * @see java.lang.Object#toString()
   * @return string representation
   */
  @Override
  public final String toString() {
    String string = my_featureType + "\n"; //$NON-NLS-1$
    if (my_precondition.size() > 0) {
      string += "\trequires \n"; //$NON-NLS-1$
      for (final Expression s : my_precondition) {
        if (s.skip()) {
          string += "\t (* " + s + " *)\n"; //$NON-NLS-1$ //$NON-NLS-2$
        } else {
          string += "\t" + s + "\n"; //$NON-NLS-1$ //$NON-NLS-2$
        }
      }
    }
    if (my_postcondition.size() > 0) {
      string += "\tensures \n\t"; //$NON-NLS-1$
      for (final Expression s : my_postcondition) {
        if (s.skip()) {
          string += "\t (* " + s + " *)\n"; //$NON-NLS-1$ //$NON-NLS-2$
        } else {
          string += "\t" + s + "\n"; //$NON-NLS-1$ //$NON-NLS-2$
        }
      }
    }
    if (my_frame.size() > 0) {
      string += "\tmodifies: " + my_frame + "\n"; //$NON-NLS-1$ //$NON-NLS-2$
    }
    if (my_constantValue != null) {
      string += "\tconstant value : " + my_constantValue + "\n"; //$NON-NLS-1$ //$NON-NLS-2$
    }
    return string;
  }

  /**
   * Is this specification empty.
   * @return true if no pre or postconditions, no frame condition
   * no constant value and no feature type
   */
  public final boolean isEmpty() {
    if (my_precondition.size() == 0 && my_postcondition.size() == 0 &&
        my_frame.size() == 0 && my_constantValue == null &&
        my_featureType == FeatureType.UNKNOWN) {
      return true;
    }
    return false;
  }

  /**
   * Is this feature pure.
   * @return true if this is a query
   */
  public final boolean isPure() {
    return my_featureType == FeatureType.QUERY;
  }

}
