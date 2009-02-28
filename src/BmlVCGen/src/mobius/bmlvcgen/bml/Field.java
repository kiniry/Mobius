package mobius.bmlvcgen.bml;

import java.util.EnumSet;

/**
 * Field declaration.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface Field {
  /**
   * Field access flags.
   */
  enum AccessFlag {
    /**
     * Declared public; may be accessed from outside its package.
     */
    ACC_PUBLIC(0x0001), 
    /**
     * Declared private; usable only within the defining class.
     */
    ACC_PRIVATE(0x0002), 
    /**
     * Declared protected; may be accessed within subclasses.
     */
    ACC_PROTECTED(0x0004), 
    /** Declared static. */
    ACC_STATIC(0x0008), 
    /** 
     * Declared final; no further assignment after initialization.
     */
    ACC_FINAL(0x0010), 
    /**
     * Declared volatile; cannot be cached.
     */
    ACC_VOLATILE(0x0040), 
    /**
     * Declared transient; not written or read 
     * by a persistent object manager.
     */
    ACC_TRANSIENT(0x0080), 
    /** Declared synthetic; Not present in the source code. */
    ACC_SYNTHETIC(0x1000), 
    /** Declared as an element of an enum. */
    ACC_ENUM(0x4000);
    
    private final int value;
    
    AccessFlag(final int value) {
      this.value = value;
    }
    
    /**
     * Convert mask to set of field AccessFlag values.
     * @param mask Mask.
     */
    public static EnumSet<AccessFlag> fromMask(final int mask) {
      final EnumSet<AccessFlag> result = 
        EnumSet.noneOf(AccessFlag.class);
      for (final AccessFlag flag : AccessFlag.values()) {
        if ((flag.value & mask) != 0) {
          result.add(flag);
        }
      }
      return result;
    }
    
    /** 
     * Get value associated with this field flag.
     * @return Flag value (as defined in JSR202).
     */
    public int getValue() {
      return value;
    }
  }
  
  /**
   * Visit this declaration.
   * @param v Visitor.
   */
  void accept(FieldVisitor v);
}
