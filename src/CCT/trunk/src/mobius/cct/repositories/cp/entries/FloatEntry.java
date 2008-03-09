package mobius.cct.repositories.cp.entries;

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
  @Override
  public int getType() {
    return CONSTANT_Float;
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
   * Equality test.
   * @param obj Object to be compared.
   */
  @Override
  public boolean equals(Object obj) {
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
