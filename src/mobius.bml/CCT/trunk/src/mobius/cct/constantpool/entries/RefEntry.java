package mobius.cct.constantpool.entries;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Abstract base class of entries which consist of
 * class name and a signature.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class RefEntry implements Entry {
  /** Index of class name in constant pool. */
  private int fClassName;
  
  /** Index of field name and type info in constant pool. */
  private int fSignature;
  
  /**
   * Create entry. 
   * @param className Index of class name in constant pool.
   * Should point to an entry of type CONSTANT_Class.
   * @param signature Index of name and type info.
   * Should point to an entry of type CONSTANT_NameAndType.
   */
  protected RefEntry(final int className, 
                     final int signature) {
    fClassName = className;
    fSignature = signature;
  }
  
  /**
   * Get size. Default value is 1, but this can
   * be changed in a subclass.
   * @return Entry size.
   */
  public int getSize() {
    return 1;
  }
  
  /**
   * Write RefEntry to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final OutputStream os) throws IOException {
    final DataOutputStream ds = new DataOutputStream(os);
    ds.writeShort(fClassName);
    ds.writeShort(fSignature);
  }
  
  /**
   * Return constant pool index of class name.
   * @return Index.
   */
  public int getClassName() {
    return fClassName;
  }
  
  /**
   * Return constant pool index of name and type info.
   * @return Index.
   */
  public int getSignature() {
    return fSignature;
  }

  /**
   * Test equality of RefEntries.
   * @param obj Object to be compared.
   * @return true iff this equeals obj.
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    } else if (obj.getClass().equals(this.getClass())) {
      return fClassName == ((RefEntry)obj).getClassName() &&
        fSignature == ((RefEntry)obj).getSignature();
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
    return (fSignature << 16) + fClassName;
  }
  
}
