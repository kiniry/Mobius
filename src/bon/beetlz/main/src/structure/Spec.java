/**
 * Package for data structures.
 */
package structure;

import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Vector;

import logic.BeetlzExpression;
import logic.BeetlzExpression.Keyword;
import logic.BeetlzExpression.Keyword.Keywords;
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
  private final List < BeetlzExpression > my_precondition;
  /** Postcondition.  */
  private final List < BeetlzExpression > my_postcondition;
  /** Frame condition. */
  //private final SortedSet < FeatureSmartString > my_frame;
  private final List < BeetlzExpression > my_frame;
  /** A constant value if the feature/method is constant. */
  private final /*@ nullable @*/ String my_constantValue;
  /** Feature type: field, query, command, mixed, unknown. */
  private final FeatureType my_featureType;


  /**
   * Dummy specs.
   */
  public Spec() {
    my_precondition = new Vector < BeetlzExpression > ();
    my_postcondition = new Vector < BeetlzExpression > ();
    my_frame = new Vector < BeetlzExpression > ();
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
  public Spec(final List < BeetlzExpression > a_pre,
              final List < BeetlzExpression > a_post,
              final List < BeetlzExpression > a_frame,
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
  public final List < BeetlzExpression > getPreconditions() {
    return my_precondition;
  }

  /**
   * Get all non informal preconditions.
   * @return non informal preconditions
   */
  public final List < BeetlzExpression > getNonTrivialPreconditions() {
    final List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
    for (final BeetlzExpression e : my_precondition) {
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
  public final List < BeetlzExpression > getInformalPreconditions() {
    final List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
    for (final BeetlzExpression e : my_precondition) {
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
  public final List < BeetlzExpression > getNonTrivialPostconditions() {
    final List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
    for (final BeetlzExpression e : my_postcondition) {
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
  public final List < BeetlzExpression > getInformalPostconditions() {
    final List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
    for (final BeetlzExpression e : my_postcondition) {
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
  public final List < BeetlzExpression > getPostconditions() {
    return my_postcondition;
  }

  /**
   * Get frame conditions.
   * @return the frame
   */
  public final List < BeetlzExpression > getFrame() {
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
        (my_frame.get(0).compareToTyped(new Keyword(Keywords.NOTHING)) == 0);
    } else if (my_type == ClassType.JAVA) {
      return my_frame.size() == 1 &&
        (my_frame.get(0).compareToTyped(new Keyword(Keywords.EVERYTHING)) == 0);
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
      if ((my_frame.get(0).compareToTyped(new Keyword(Keywords.EVERYTHING)) == 0) ||
          (my_frame.get(0).compareToTyped(new Keyword(Keywords.NOTHING)) == 0)) {
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
      for (final BeetlzExpression s : my_precondition) {
        if (s.skip()) {
          string += "\t (* " + s + " *)\n"; //$NON-NLS-1$ //$NON-NLS-2$
        } else {
          string += "\t" + s + "\n"; //$NON-NLS-1$ //$NON-NLS-2$
        }
      }
    }
    if (my_postcondition.size() > 0) {
      string += "\tensures \n\t"; //$NON-NLS-1$
      for (final BeetlzExpression s : my_postcondition) {
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
