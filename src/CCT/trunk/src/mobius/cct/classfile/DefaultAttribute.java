package mobius.cct.classfile;

import java.io.DataInputStream;
import java.io.IOException;
import java.io.OutputStream;

import mobius.cct.constantpool.ConstantPool;
import mobius.cct.constantpool.DefaultPool;
import mobius.cct.repositories.InvalidFormatException;

/**
 * Default implementation of attribute interface.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultAttribute implements Attribute {
  /**
   * Name.
   */
  private final String fName;
  
  /**
   * Data.
   */
  private final byte[] fData;
  
  /**
   * Constructor - read attribute from stream.
   * @param ds Input stream.
   * @param cp Constant pool.
   * @throws IOException .
   */
  public DefaultAttribute(final DataInputStream ds, 
                          final ConstantPool cp) throws IOException {
    final int nameIndex = ds.readUnsignedShort();
    fName = DefaultPool.getString(cp, nameIndex);
    if (fName == null) {
      throw new InvalidFormatException("Invalid attribute name.");
    }
    final int size = ds.readInt();
    fData = new byte[size];
    ds.readFully(fData);
  }
  
  /**
   * Constructor - create attribute from byte array.
   * @param t Attribute type.
   * @param data Attribute data.
   */
  public DefaultAttribute(final String t, final byte[] data) {
    fName = t;
    fData = data;
  }
  
  /**
   * Get attribute name.
   * @return Name.
   */
  public String getName() {
    return fName;
  }

  /**
   * Write data to an output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void writeData(final OutputStream os) 
    throws IOException {
    os.write(fData);
  }
  
}
