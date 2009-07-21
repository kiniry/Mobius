/**
 * Package for data structures.
 */
package structure;

import java.util.List;
import java.util.Vector;

import utils.ModifierManager.VisibilityModifier;
import utils.smart.TypeSmartString;

/**
 * Data structure for visibility issues.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class Visibility {
  /** Modifier. */
  private final VisibilityModifier my_modifier;
  /** Visibility for specifications. */
  private VisibilityModifier my_specVisibility;
  /**
   * Classes that have access to this class or feature.
   * In BON these are explicitly mentioned.
   * In Java package-private or protected we get all classes
   * inside the package.
   */
  private List < TypeSmartString > my_exports;

  /**
   * Creates a new visibility with both specs and
   * actual visibility being equal.
   * @param a_visibility visibility
   */
  public Visibility(final VisibilityModifier a_visibility) {
    my_modifier = a_visibility;
    my_specVisibility = a_visibility;
    my_exports = new Vector < TypeSmartString > ();
  }

  /**
   * Get the actual visibility.
   * @return the modifier
   */
  public final VisibilityModifier getActualVisibility() {
    return my_modifier;
  }

  /**
   * Get the specification visibility.
   * @return specs visibility
   */
  public final VisibilityModifier getSpecVisibility() {
    return my_specVisibility;
  }

  /**
   * Get exports.
   * @return the exports
   */
  public final List < TypeSmartString > getExports() {
    return my_exports;
  }

  /**
   * Set the specification visibility.
   * @param a_modifier specs visibility
   */
  public final void setSpecVisibility(final VisibilityModifier a_modifier) {
    my_specVisibility = a_modifier;
  }

  /**
   * Set the exports.
   * @param some_exports the exports to set
   */
  public final void setExports(final List < TypeSmartString > some_exports) {
    my_exports = some_exports;
  }


}
