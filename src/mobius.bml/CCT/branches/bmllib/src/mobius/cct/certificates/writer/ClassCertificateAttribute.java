package mobius.cct.certificates.writer;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Iterator;

import mobius.cct.certificates.ClassCertificate;
import mobius.cct.classfile.Attribute;
import mobius.cct.constantpool.ConstantPoolBuilder;

/**
 * A class ertificate wrapped in Attribute interface.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ClassCertificateAttribute implements Attribute {
  /**
   * Certificate.
   */
  private final ClassCertificate fCert;
  
  /**
   * Second constant pool.
   */
  private final ConstantPoolBuilder fSCP;
  
  /**
   * Constructor.
   * @param cert Certificate.
   * @param scp Second constant pool.
   */
  public ClassCertificateAttribute(final ClassCertificate cert,
                                   final ConstantPoolBuilder scp) {
    fCert = cert;
    fSCP = scp;
  }

  /**
   * Get attribute name.
   * @return ClassCertificate.ATTR.
   */
  public String getName() {
    return ClassCertificate.ATTR;
  }

  /**
   * Write certificate to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void writeData(final OutputStream os) throws IOException {
    final DataOutputStream ds = new DataOutputStream(os);
    ds.writeShort(fSCP.newUtf8(fCert.getType()));
    ds.writeByte(fCert.getVersion().getMajor());
    ds.writeByte(fCert.getVersion().getMinor());
    ds.writeShort(fCert.getImportCount());
    final Iterator<String> i = fCert.getImports();
    while (i.hasNext()) {
      ds.writeShort(fSCP.newUtf8(i.next()));
    }
    final byte[] data = fCert.getData();
    ds.writeInt(data.length);
    ds.write(data);
  }
}
