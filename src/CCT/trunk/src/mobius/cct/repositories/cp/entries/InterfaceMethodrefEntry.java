package mobius.cct.repositories.cp.entries;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Interface method reference.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class InterfaceMethodrefEntry implements Entry {
  /** Index of class name in constant pool. */
  private int fClassName;
  
  /** Index of method name and type info in constant pool. */
  private int fSignature;
  
  /**
   * Create entry. 
   * @param className Index of class name in constant pool.
   * Should point to an entry of type CONSTANT_Class.
   * @param signature Index of name and type info.
   * Should point to an entry of type CONSTANT_NameAndType.
   */
  public InterfaceMethodrefEntry(final int className, 
                        final int signature) {
    fClassName = className;
    fSignature = signature;
  }
  
  /**
   * Get entry type.
   * @return CONSTANT_InterfaceMethodref.
   */
  @Override
  public int getType() {
    return CONSTANT_InterfaceMethodref;
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
   * Equality test.
   * @param obj Object to be compared.
   */
  @Override
  public boolean equals(Object obj) {
    if (obj == null) {
      return false;
    } else if (obj.getClass().equals(this.getClass())) {
      return 
        fClassName == ((InterfaceMethodrefEntry)obj).getClassName() &&
        fSignature == ((InterfaceMethodrefEntry)obj).getSignature();
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
