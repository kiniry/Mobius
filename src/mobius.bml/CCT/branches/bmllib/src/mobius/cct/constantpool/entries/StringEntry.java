package mobius.cct.constantpool.entries;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/**
 * String constant.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class StringEntry implements Entry {
  
  /** Index of string value name in constant pool. */
  private int fValue;
  
  /**
   * Create entry.
   * @param value Index of string value in constant pool.
   * This should point to an entry of type CONSTANT_Utf8.
   */
  public StringEntry(final int value) {
    fValue = value;
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_String.
   */
  public byte getType() {
    return CONSTANT_String;
  }
  
  /**
   * Get size.
   * @return 1.
   */
  public int getSize() {
    return 1;
  }
  
  /**
   * Write StringEntry to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final OutputStream os) throws IOException {
    final DataOutputStream ds = new DataOutputStream(os);
    ds.writeShort(fValue);
  }
  
  /**
   * Return constant pool index of string value.
   * @return Index.
   */
  public int getValue() {
    return fValue;
  }
  
  /**
   * Test equality of StringEntries.
   * @param obj Object to be compared.
   * @return true iff this equals obj.
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    } else if (obj.getClass().equals(this.getClass())) {
      return fValue == ((StringEntry)obj).getValue();
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
    return fValue;
  }
}
