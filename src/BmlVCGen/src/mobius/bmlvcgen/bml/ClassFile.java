package mobius.bmlvcgen.bml;

import java.util.EnumSet;

/**
 * Objects implementing this interface 
 * represent class files.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface ClassFile {
  /**
   * Class access flags.
   */
  enum AccessFlag {
    /**
     * Declared public; may be accessed
     * from outside its package.
     */
    ACC_PUBLIC(0x0001), 
    /**    
     * Declared final; no subclasses allowed.
     */
    ACC_FINAL(0x0010), 
    /**
     * Treat superclass methods specially
     * when invoked by the invokespecial
     * instruction.
     */
    ACC_SUPER(0x0020), 
    /** Is an interface, not a class. */
    ACC_INTERFACE(0x0200), 
    /** Declared abstract; must not be instantiated. */
    ACC_ABSTRACT(0x0400),
    /** Declared synthetic; Not present in the source code. */
    ACC_SYNTHETIC(0x1000), 
    /** Declared as an annotation type. */
    ACC_ANNOTATION(0x2000), 
    /** Declared as an enum type. */
    ACC_ENUM(0x4000);
    
    private final int value;
    
    AccessFlag(final int value) {
      this.value = value;
    }
    
    /**
     * Convert mask to set of class AccessFlag values.
     * @param mask Mask.
     */
    public static EnumSet<AccessFlag> fromMask(final int mask) {
      final EnumSet<AccessFlag> result = 
        EnumSet.noneOf(AccessFlag.class);
      for (final AccessFlag flag : AccessFlag.values()) {
        //
        if ((flag.value & mask) != 0) {
          result.add(flag);
        }
      }
      return result;
    }
    
    /** 
     * Get value associated with this class flag.
     * @return Flag value (as defined in JSR202).
     */
    public int getValue() {
      return value;
    }

  }
  
  /**
   * Visibility modifiers associated with
   * fields, methods, invariants etc.
   */
  enum Visibility {
    /** Visible only inside package. */
    DEFAULT,
    /** Visible outside package. */
    PUBLIC,
    /** Visible in subclasses. */
    PROTECTED,
    /** Private. */
    PRIVATE
  }
  
  /**
   * Use a visitor to visit this class file.
   * @param v Visitor.
   */
  void accept(ClassVisitor v);
}
