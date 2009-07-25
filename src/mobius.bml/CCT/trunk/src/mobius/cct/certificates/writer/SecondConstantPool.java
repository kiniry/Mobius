package mobius.cct.certificates.writer;

import java.io.IOException;
import java.io.OutputStream;
import java.util.Iterator;

import mobius.cct.classfile.Attribute;
import mobius.cct.constantpool.ConstantPool;
import mobius.cct.constantpool.IllegalIndexException;
import mobius.cct.constantpool.entries.Entry;

/**
 * Constant pool stored in an attribute.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class SecondConstantPool implements ConstantPool, Attribute {
  /**
   * Attribute name.
   */
  public static final String ATTR = "org.bmlspecs.ThirdConstantPool";
  
  /**
   * Source constant pool.
   */
  private final ConstantPool fSource;
  
  /**
   * Constructor.
   * @param source Constant pool to be wrapped as SCP.
   */
  public SecondConstantPool(final ConstantPool source) {
    fSource = source;
  }
  
  /**
   * Delegated to source pool.
   * @param index Entry index.
   * @return Entry.
   * @throws IllegalIndexException .
   */
  public Entry getEntry(final int index) 
    throws IllegalIndexException {
    return fSource.getEntry(index);
  }

  /**
   * Get size.
   * @return size.
   */
  public int getSize() {
    return fSource.getSize();
  }

  /**
   * Get entries.
   * @return Iterator.
   */
  public Iterator<Entry> iterator() {
    return fSource.iterator();
  }

  /**
   * Write constant pool.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final OutputStream os) 
    throws IOException {
    fSource.write(os);
  }

  /**
   * Get attribute name.
   * @return "org.bmlspecs.ThirdConstantPool".
   */
  public String getName() {
    return ATTR;
  }

  /**
   * Write attribute data to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void writeData(final OutputStream os) throws IOException {
    fSource.write(os);
  }

}
