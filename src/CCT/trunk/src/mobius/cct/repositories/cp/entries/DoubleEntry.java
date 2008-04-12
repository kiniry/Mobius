package mobius.cct.repositories.cp.entries;

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
  @Override
  public byte getType() {
    return CONSTANT_Double;
  }
  
  /**
   * Get size.
   * @return 2.
   */
  @Override
  public int getSize() {
    return 2;
  }
  
  /**
   * Write to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  @Override
  public void write(final OutputStream os) throws IOException {
    DataOutputStream ds = new DataOutputStream(os);
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
   * Equality test.
   * @param obj Object to be compared.
   */
  @Override
  public boolean equals(Object obj) {
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
