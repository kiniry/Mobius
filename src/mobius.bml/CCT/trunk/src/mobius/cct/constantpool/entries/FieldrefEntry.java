package mobius.cct.constantpool.entries;

/**
 * Field reference.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class FieldrefEntry extends RefEntry {
 
  /**
   * Create entry. 
   * @param className Index of class name in constant pool.
   * Should point to an entry of type CONSTANT_Class.
   * @param signature Index of name and type info.
   * Should point to an entry of type CONSTANT_NameAndType.
   */
  public FieldrefEntry(final int className, 
                       final int signature) {
    super(className, signature);
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_Fieldref.
   */
  public byte getType() {
    return CONSTANT_Fieldref;
  }
  
}
