package annot.attributes;


/**
 * Contains codes for each printable attribute type
 * and commonly used bit masks to represent sets of attributes
 * that we want retrieve (through getAllAttribute(int mask) methods).
 * TODO w czym te kody sa wykorzystywane?
 *
 * @see BCClass#getAllAttributes(int)
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public final class AType {

  // attribute masks:

  /**
   * Attribute mask that admits all the attribute types.
   */
  public static final int C_ALL = 0xffffffff;

  // attribute codes (must be in (1 << n) form, for n=0,1,2,...)

  /**
   * Type value for a single assert.
   */
  public static final int C_ASSERT = 1;

  /**
   * The value for a class invariant.
   */
  public static final int C_CLASSINVARIANT = 4;

  /**
   * The value for the loop specification.
   */
  public static final int C_LOOPSPEC = 8;

  /**
   * The value for method specification.
   */
  public static final int C_METHODSPEC = 2;

  /**
   * An empty private constructor to forbid the creation of instances.
   */
  private AType() {
  }

}
