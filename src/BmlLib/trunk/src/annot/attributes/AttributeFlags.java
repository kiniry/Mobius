/**
 * 
 */
package annot.attributes;

/**
 * @author alx
 *
 */
public class AttributeFlags {

  /**
   * The encoding of the flag which indicates that a BML entity is
   * public. See section "Encoding of Modifiers" in "BML Reference Manual".
   */
  public static int ACC_PUBLIC = 0x00000001;

  /**
   * The encoding of the flag which indicates that a BML entity is
   * protected. See section "Encoding of Modifiers" in "BML Reference Manual".
   */
  public static int ACC_PROTECTED = 0x00000004;

  /**
   * The encoding of the flag which indicates that a BML entity is
   * private. FIXME: no support in BML Refman
   */
  public static int ACC_PRIVATE = 0x00000008;

  /**
   * The encoding of the flag which indicates that a BML entity is
   * private. FIXME: no support in BML Refman
   */
  public static int ACC_STATIC = 0x00000010;
  
}
