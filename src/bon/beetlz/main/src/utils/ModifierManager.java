/**
 * Package for utility classes.
 */
package utils;

/**
 * Collection of modifier enums.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class ModifierManager {

  /**
   * Enumerated type for feature modifier.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public enum FeatureModifier {
    /** Java modifier. */
    ABSTRACT("abstract"), //$NON-NLS-1$
    /** Java modifier. */
    STATIC("static"), //$NON-NLS-1$
    /** Java modifier. */
    FINAL("final"),  //$NON-NLS-1$
    /** Java modifier. */
    STRICTFP("strictfp"), //$NON-NLS-1$
    /** Java modifier. */
    SYNCHRONIZED("synchronized"), //$NON-NLS-1$
    /** Java modifier. */
    TRANSIENT("transient"), //$NON-NLS-1$
    /** Java modifier. */
    VOLATILE("volatile"), //$NON-NLS-1$
    /** Java modifier. */
    NATIVE("native"), //$NON-NLS-1$
    /** BON modifier. */
    EFFECTIVE("effective"), //$NON-NLS-1$
    /** BON modifier. */
    REDEFINED("redefined"), //$NON-NLS-1$
    /** BON modifier. */
    PURE("/*@ pure @*/"), //$NON-NLS-1$
    /** BON modifier. */
    IMPLEMENTED("implemented"), //$NON-NLS-1$
    /** BON modifier. */
    CONSTANT("constant"), //$NON-NLS-1$
    /** BON modifier. */
    MODEL("model"), //$NON-NLS-1$
    /** BON modifier. */
    GHOST("ghost"); //$NON-NLS-1$

    /**
     * Modifier.
     */
    private final String my_feature_modifier;

    /**
     * Constructor.
     * @param a_name modifier type
     */
    private FeatureModifier(final String a_name) {
      my_feature_modifier = a_name;
    }

    /**
     * Returns the modifier in lower case written form.
     * @return String representation of modifier
     */
    public String getName() {
      return my_feature_modifier;
    }

    /**
     * Returns the modifier in lower case written form.
     * @see java.lang.Enum#toString()
     * @return String representation of modifier
     */
    @Override
    public String toString() {
      return my_feature_modifier;
    }

  } //end enum

  /**
   * Visibility modifier.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public enum VisibilityModifier {
    /** Java modifier. */
    PUBLIC("public"), //$NON-NLS-1$
    /** Java modifier. */
    PROTECTED("protected"), //$NON-NLS-1$
    /** Java modifier. */
    PACKAGE_PRIVATE("package_private"), //$NON-NLS-1$
    /** BON modifier. */
    RESTRICTED("restricted"), //$NON-NLS-1$
    /** BON modifier. */
    PRIVATE("private");  //$NON-NLS-1$

    /**
     * Modifier.
     */
    private final String my_visibility_modifier;

    /**
     * Constructor.
     * @param a_name modifier type
     */
    VisibilityModifier(final String a_name) {
      my_visibility_modifier = a_name;
    }

    /**
     * Returns the modifier in lower case written form.
     * @return String representation of modifier
     */
    public String getName() {
      return my_visibility_modifier;
    }

    /**
     * Returns the modifier in lower case written form.
     * @see java.lang.Enum#toString()
     * @return String representation of modifier
     */
    @Override
    public String toString() {
      return my_visibility_modifier;
    }

  } //end enum

  /**
   * Class modifier.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public enum ClassModifier {
    /** Java modifier. */
    ABSTRACT("abstract"), //$NON-NLS-1$
    /** Java modifier. */
    STATIC("static"), //$NON-NLS-1$
    /** Java modifier. */
    FINAL("final"), //$NON-NLS-1$
    /** Java modifier. */
    STRICTFP("strictfp"), //$NON-NLS-1$
    /** BON modifier. */
    REUSED("reused"), //$NON-NLS-1$
    /** BON modifier. */
    PERSISTENT("persistent"), //$NON-NLS-1$
    /** BON modifier. */
    INTERFACED("interfaced"),  //$NON-NLS-1$
    /** BON modifier. */
    EFFECTIVE("effective"), //$NON-NLS-1$
    /** BON modifier. */
    ROOT("root"), //$NON-NLS-1$
    /** Helper modifier. */
    GENERIC("generic"), //$NON-NLS-1$
    /** Helper modifier. */
    ENUM("enum"), //$NON-NLS-1$
    /** Helper modifier. */
    JAVA_INTERFACE("interface"); //$NON-NLS-1$

    /**
     * Class modifier.
     */
    private final String my_class_modifier;

    /**
     * Constructor.
     * @param a_name name
     */
    private ClassModifier(final String a_name) {
      this.my_class_modifier = a_name;
    }

    /**
     * Returns the modifier in lower case written form.
     * @return String representation of modifier
     */
    public String getName() {
      return my_class_modifier;
    }

    /**
     * Returns the modifier in lower case written form.
     * @see java.lang.Enum#toString()
     * @return String representation of modifier
     */
    @Override
    public String toString() {
      return my_class_modifier;
    }
  } //end enum Modifier

  /**
   * Class type.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public enum ClassType {
    /** What kind of class. */
    BON("bon"), JAVA("java"), //$NON-NLS-1$
    /** Not specified. */
    NOT_SPECIFIED("not specified"); //$NON-NLS-1$

    /** Modifier. */
    private final String my_modifier;

    /**
     * Constructor.
     * @param a_name name
     */
    private ClassType(final String a_name) {
      this.my_modifier = a_name;
    }


    /**
     * Returns the modifier in lower case written form.
     * @see java.lang.Enum#toString()
     * @return String representation of modifier
     */
    @Override
    public String toString() {
      return my_modifier;
    }
  } //end enum Modifier

}
