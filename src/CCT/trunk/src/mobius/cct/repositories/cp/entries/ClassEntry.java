package mobius.cct.repositories.cp.entries;

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
  @Override
  public byte getType() {
    return CONSTANT_Class;
  }
  
  /**
   * Get size.
   * @return 1.
   */
  @Override
  public int getSize() {
    return 1;
  }
  
  /**
   * Write to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  @Override
  public void write(final OutputStream os) throws IOException {
    DataOutputStream ds = new DataOutputStream(os);
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
   * Equality test.
   * @param obj Object to be compared.
   */
  @Override
  public boolean equals(Object obj) {
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
