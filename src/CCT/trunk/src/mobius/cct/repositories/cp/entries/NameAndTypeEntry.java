package mobius.cct.repositories.cp.entries;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Signature of field or method.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class NameAndTypeEntry implements Entry {
  /**
   * Constant pool index of field/method name.
   */
  private int fName;
  
  /**
   * Constant pool index field/method type.
   */
  private int fTypeIndex;
  
  /**
   * Create entry.
   * @param name Index of field/method name (CONSTANT_Utf8).
   * @param typeIndex Index of field/method type (CONSTANT_Utf8).
   */
  public NameAndTypeEntry(final int name, final int typeIndex) {
    fName = name;
    fTypeIndex = typeIndex;
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_NameAndType.
   */
  @Override
  public byte getType() {
    return CONSTANT_NameAndType;
  }
  
  /**
   * Get size.
   * @return 2.
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
    ds.writeShort(fTypeIndex);
  }
  
  /**
   * Return name index.
   * @return Index.
   */
  public int getName() {
    return fName;
  }
  
  /**
   * Return type index.
   * @return Index.
   */
  public int getTypeIndex() {
    return fTypeIndex;
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
      return fName == ((NameAndTypeEntry)obj).getName() && 
        fTypeIndex == ((NameAndTypeEntry)obj).getTypeIndex();
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
    return (fTypeIndex << 16) + fName;
  }
}
