package mobius.cct.bmllib;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.ConstantUtf8;

import mobius.cct.classfile.Attribute;

/**
 * Wrapper for BCEL attributes.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class BmlAttribute implements Attribute {
  // Wrapped attribute.
  private final  org.apache.bcel.classfile.Attribute attr;

  /** 
   * Constructor.
   * @param attr Attribute to be wrapped.
   */
  public BmlAttribute(
      final org.apache.bcel.classfile.Attribute attr) {
    this.attr = attr;
  }
  
  /** {@inheritDoc} */
  @Override
  public String getName() {
    final ConstantUtf8 con = 
      (ConstantUtf8)attr.getConstantPool().
        getConstant(attr.getNameIndex());
    return con.getBytes();
  }

  /** {@inheritDoc} */
  @Override
  public void writeData(final OutputStream os) 
    throws IOException {
    ByteArrayOutputStream bos = 
      new ByteArrayOutputStream();
    DataOutputStream ds = new DataOutputStream(bos);
    attr.dump(ds);
    ds.close();
    // Cut name and length... stupid.
    assert(bos.size() == attr.getLength() + 6);
    os.write(bos.toByteArray(), 6, attr.getLength());
  }
}
