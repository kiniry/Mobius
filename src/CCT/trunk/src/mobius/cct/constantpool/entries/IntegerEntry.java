package mobius.cct.constantpool.entries;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Integer (32-bit).
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class IntegerEntry implements Entry {
  /** Integer value. */
  private int fValue;
  
  /**
   * Create entry.
   * @param value Integer value.
   */
  public IntegerEntry(final int value) {
    fValue = value;
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_Integer.
   */
  public byte getType() {
    return CONSTANT_Integer;
  }
  
  /**
   * Get size.
   * @return 1.
   */
  public int getSize() {
    return 1;
  }
  
  /**
   * Write IntegerEntry to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final OutputStream os) throws IOException {
    final DataOutputStream ds = new DataOutputStream(os);
    ds.writeInt(fValue);
  }
  
  /**
   * Return integer value.
   * @return Value.
   */
  public int getValue() {
    return fValue;
  }
  
  /**
   * Test equality of IntegerEntries.
   * @param obj Object to be compared.
   * @return true iff this equals obj.
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    } else if (obj.getClass().equals(this.getClass())) {
      return fValue == ((IntegerEntry)obj).getValue();
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
