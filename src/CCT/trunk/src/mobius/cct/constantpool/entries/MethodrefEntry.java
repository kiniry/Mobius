package mobius.cct.constantpool.entries;

/**
 * Method reference.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class MethodrefEntry extends RefEntry {
  /**
   * Create entry. 
   * @param className Index of class name in constant pool.
   * Should point to an entry of type CONSTANT_Class.
   * @param signature Index of name and type info.
   * Should point to an entry of type CONSTANT_NameAndType.
   */
  public MethodrefEntry(final int className, 
                        final int signature) {
    super(className, signature);
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_Methodref.
   */
  public byte getType() {
    return CONSTANT_Methodref;
  }

}
