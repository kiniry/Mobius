package mobius.cct.constantpool.entries;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Long float (64-bit).
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class DoubleEntry implements Entry {
  /** Float value. */
  private double fValue;
  
  /**
   * Create entry.
   * @param value Float value.
   */
  public DoubleEntry(final double value) {
    fValue = value;
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_Double.
   */
  public byte getType() {
    return CONSTANT_Double;
  }
  
  /**
   * Get size.
   * @return 2.
   */
  public int getSize() {
    return 2;
  }
  
  /**
   * Write DoubleEntry to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final OutputStream os) throws IOException {
    final DataOutputStream ds = new DataOutputStream(os);
    ds.writeDouble(fValue);
  }
  
  /**
   * Return float value.
   * @return Value.
   */
  public double getValue() {
    return fValue;
  }
  
  /**
   * Test equality of DoubleEntries.
   * @param obj Object to be compared.
   * @return true iff this equals obj.
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    } else if (obj.getClass().equals(this.getClass())) {
      return fValue == ((DoubleEntry)obj).getValue();
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
    return new Double(fValue).hashCode();
  }
}
