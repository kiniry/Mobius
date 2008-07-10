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
  byte CONSTANT_Class = 7;

  /** Field reference. */
  byte CONSTANT_Fieldref = 9;

  /** Method reference. */
  byte CONSTANT_Methodref = 10;

  /** Interface method reference. */
  byte CONSTANT_InterfaceMethodref = 11;

  /** String constant. */
  byte CONSTANT_String = 8;

  /** 32-bit integer. */
  byte CONSTANT_Integer = 3;

  /** 32-bit float. */
  byte CONSTANT_Float = 4;

  /** 64-bit integer. */
  byte CONSTANT_Long = 5;

  /** 64-bit float. */
  byte CONSTANT_Double = 6;

  /** Field or method signature. */
  byte CONSTANT_NameAndType = 12;

  /** String encoded in modified UTF8. */
  byte CONSTANT_Utf8 = 1;

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
