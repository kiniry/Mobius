package mobius.cct.constantpool.entries;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Float (32-bit).
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class FloatEntry implements Entry {
  /** Float value. */
  private float fValue;
  
  /**
   * Create entry.
   * @param value Integer value.
   */
  public FloatEntry(final float value) {
    fValue = value;
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_Float.
   */
  public byte getType() {
    return CONSTANT_Float;
  }
  
  /**
   * Get size.
   * @return 1.
   */
  public int getSize() {
    return 1;
  }
  
  /**
   * Write FloatEntry to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final OutputStream os) throws IOException {
    final DataOutputStream ds = new DataOutputStream(os);
    ds.writeFloat(fValue);
  }
  
  /**
   * Return float value.
   * @return Value.
   */
  public float getValue() {
    return fValue;
  }
  
  /**
   * Test equality of FloatEntries.
   * @param obj Object to be compared.
   * @return true iff this equals obj.
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    } else if (obj.getClass().equals(this.getClass())) {
      return fValue == ((FloatEntry)obj).getValue();
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
    return new Float(fValue).hashCode();
  }
}
