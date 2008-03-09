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
  public static final int CONSTANT_Class = 7;

  /** Field reference. */
  public static final int CONSTANT_Fieldref = 9;

  /** Method reference. */
  public static final int CONSTANT_Methodref = 10;

  /** Interface method reference. */
  public static final int CONSTANT_InterfaceMethodref = 11;

  /** String constant. */
  public static final int CONSTANT_String = 8;

  /** 32-bit integer. */
  public static final int CONSTANT_Integer = 3;

  /** 32-bit float. */
  public static final int CONSTANT_Float = 4;

  /** 64-bit integer. */
  public static final int CONSTANT_Long = 5;

  /** 64-bit float. */
  public static final int CONSTANT_Double = 6;

  /** Field or method signature. */
  public static final int CONSTANT_NameAndType = 12;

  /** String encoded in modified UTF8. */
  public static final int CONSTANT_Utf8 = 1;

  /**
   * Return entry type.
   * 
   * @return Entry type.
   */
  int getType();
  
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
