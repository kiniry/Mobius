package mobius.cct.repositories.cp.entries;

import java.io.OutputStream;
import java.io.IOException;

/**
 * Constant pool entry. All entries must also override equals()
 * and hashcode().
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface Entry {
  /* Entry types defined in JSR-202 */
  
  /** Class or interface name. */
  public static final byte CONSTANT_Class = 7;

  /** Field reference. */
  public static final byte CONSTANT_Fieldref = 9;

  /** Method reference. */
  public static final byte CONSTANT_Methodref = 10;

  /** Interface method reference. */
  public static final byte CONSTANT_InterfaceMethodref = 11;

  /** String constant. */
  public static final byte CONSTANT_String = 8;

  /** 32-bit integer. */
  public static final byte CONSTANT_Integer = 3;

  /** 32-bit float. */
  public static final byte CONSTANT_Float = 4;

  /** 64-bit integer. */
  public static final byte CONSTANT_Long = 5;

  /** 64-bit float. */
  public static final byte CONSTANT_Double = 6;

  /** Field or method signature. */
  public static final byte CONSTANT_NameAndType = 12;

  /** String encoded in modified UTF8. */
  public static final byte CONSTANT_Utf8 = 1;

  /**
   * Return entry type.
   * 
   * @return Entry type.
   */
  byte getType();
  
  /**
   * Return entry size (how many constant pool indices it occupies).
   * 
   * @return Entry size.
   */
  int getSize();
  
  /**
   * Write entry to given output stream.
   * This method should assume that entry type
   * has already been written.
   * @param os Output stream.
   * @throws IOException .
   */
  void write(OutputStream os) throws IOException;
  
}
