package mobius.cct.constantpool.entries;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/**
 * String value.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class Utf8Entry implements Entry {
  /** String value. */
  private String fValue;
  
  /**
   * Create entry.
   * @param value String value.
   */
  public Utf8Entry(final String value) {
    fValue = value;
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_Utf8.
   */
  public byte getType() {
    return CONSTANT_Utf8;
  }
  
  /**
   * Get size.
   * @return 1.
   */
  public int getSize() {
    return 1;
  }
  
  /**
   * Write Utf8Entry to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final OutputStream os) throws IOException {
    final DataOutputStream ds = new DataOutputStream(os);
    ds.writeUTF(fValue);
  }
  
  /**
   * Return string value.
   * @return Value.
   */
  public String getValue() {
    return fValue;
  }
  
  /**
   * Test equality of Utf8Entries.
   * @param obj Object to be compared.
   * @return true iff this equals obj.
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    } else if (obj.getClass().equals(this.getClass())) {
      return fValue.equals(((Utf8Entry)obj).getValue());
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
    return fValue.hashCode();
  }
}
