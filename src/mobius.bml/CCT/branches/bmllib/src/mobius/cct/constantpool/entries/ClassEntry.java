package mobius.cct.constantpool.entries;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Class or interface.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class ClassEntry implements Entry {
  
  /** Index of class/interface name in constant pool. */
  private int fName;
  
  /**
   * Create entry. Class name is represented by constant pool
   * index of an CONSTANT_Utf8 entry. This index is not
   * validated.
   * @param name Index of class/interface name in constant pool.
   */
  public ClassEntry(final int name) {
    fName = name;
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_Class.
   */
  public byte getType() {
    return CONSTANT_Class;
  }
  
  /**
   * Get size.
   * @return 1.
   */
  public int getSize() {
    return 1;
  }
  
  /**
   * Write ClassEntry to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final OutputStream os) throws IOException {
    final DataOutputStream ds = new DataOutputStream(os);
    ds.writeShort(fName);
  }
  
  /**
   * Return constant pool index of class name.
   * @return Index.
   */
  public int getName() {
    return fName;
  }
  
  /**
   * Test equality of ClassEntries.
   * @param obj Object to be compared.
   * @return true iff this equals obj.
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    } else if (obj.getClass().equals(this.getClass())) {
      return fName == ((ClassEntry)obj).getName();
    } else {
      return false;
    }
  }
  
  /**
   * Hashcode.
   * @return Hash value.
   */
  @Override
  public int hashCode() {
    return fName;
  }
  
} 
