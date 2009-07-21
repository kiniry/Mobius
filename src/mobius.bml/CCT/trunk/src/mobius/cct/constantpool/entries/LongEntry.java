package mobius.cct.constantpool.entries;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Long integer (64-bit).
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class LongEntry implements Entry {
  /** Integer value. */
  private long fValue;
  
  /**
   * Create entry.
   * @param value Integer value.
   */
  public LongEntry(final long value) {
    fValue = value;
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_Long.
   */
  public byte getType() {
    return CONSTANT_Long;
  }
  
  /**
   * Get size.
   * @return 2.
   */
  public int getSize() {
    return 2;
  }
  
  /**
   * Write LongEntry to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final OutputStream os) throws IOException {
    final DataOutputStream ds = new DataOutputStream(os);
    ds.writeLong(fValue);
  }
  
  /**
   * Return integer value.
   * @return Value.
   */
  public long getValue() {
    return fValue;
  }
  
  /**
   * Test equality of LongEntries.
   * @param obj Object to be compared.
   * @return true iff this equals obj.
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    } else if (obj.getClass().equals(this.getClass())) {
      return fValue == ((LongEntry)obj).getValue();
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
    return Long.valueOf(fValue).hashCode();
  }
}
