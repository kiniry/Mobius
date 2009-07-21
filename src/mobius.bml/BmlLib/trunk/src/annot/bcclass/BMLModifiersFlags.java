/**
 *
 */
package annot.bcclass;


/**
 * Constants encoding the BML modifiers, described in section
 * "Encoding of Modifiers" in "BML Reference Manual". Standard JVM access
 * flags are in
 * @see org.apache.bcel.Constants
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @author Jacek Chrzaszcz (chrzaszcz@mimuw.edu.pl)
 * @version a-01
 */
public final class BMLModifiersFlags {

  /**
   * A BML modifier mask which means that none of the BML modifiers is set.
   */
  public static final int BML_NONE = 0x00000000;

  /**
   * A Java feature (method/field etc.) declared as public for specification
   * purposes. It can only be used when the feature has a more restrictive
   * visibility in Java.
   * This flag is equal to the 16-bit ACC_PUBLIC JVM flag.
   */
  public static final int BML_SPEC_PUBLIC = 0x00000001;

  /**
   * A Java feature (method/field etc.) declared as protected for
   * specification purposes. It can only be used when the feature has
   * a more restrictive visibility in Java.
   * This flag is equal to the 16-bit ACC_PROTECTED JVM flag.
   */
  public static final int BML_SPEC_PROTECTED = 0x00000004;

  /**
   * A feature (field, method result, method's parameter, local
   * variable etc.) which cannot be null.
   */
  public static final int BML_NON_NULL = 0x00000020;

  /**
   * A feature (field, method result, method's parameter, local
   * variable etc.) which can be null.
   */
  public static final int BML_NULLABLE = 0x00000040;

  /**
   * A method (or class or interface) that does not have side
   * effects.
   */
  public static final int BML_PURE = 0x00000080;

  /**
   * A method which does not have to respect invariants and history
   * constraints.
   */
  public static final int BML_HELPER = 0x00000100;

  /**
   * Ownership modifier for peer features (field, method result,
   * method's parameter, local variable etc).
   */
  public static final int BML_PEER = 0x00000400;

  /**
   * Ownership modifier for rep features (field, method result,
   * method's parameter, local variable etc).
   */
  public static final int BML_REP = 0x00000800;

  /**
   * Ownership modifier for readonly features (field, method result,
   * method's parameter, local variable etc).
   */
  public static final int BML_READONLY = 0x00001000;

  /**
   * Ownership modifier for features (field, method result, method's
   * parameter, local variable etc.) with arrays containing peer
   * elements.
   */
  public static final int BML_ELEM_PEER = 0x00002000;

  /**
   * Ownership modifier for features (field, method result, method's
   * parameter, local variable etc.) with arrays containing readonly
   * elements.
   */
  public static final int BML_ELEM_READONLY = 0x00002000;

  /**
   * Array of all the modifiers to perform the iterations over the modifiers.
   */
  public static final int[] BML_MODIFIERS = {BML_SPEC_PUBLIC,
                                             BML_SPEC_PROTECTED,
                                             BML_NON_NULL,
                                             BML_NULLABLE,
                                             BML_PURE,
                                             BML_HELPER,
                                             BML_PEER,
                                             BML_REP,
                                             BML_READONLY,
                                             BML_ELEM_PEER,
                                             BML_ELEM_READONLY
  };

  /**
   * An empty private constructor to disallow the creation of instances.
   */
  private BMLModifiersFlags() {
  }

}
