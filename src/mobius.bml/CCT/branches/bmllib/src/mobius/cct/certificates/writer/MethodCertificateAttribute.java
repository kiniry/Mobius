package mobius.cct.certificates.writer;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;

import mobius.cct.certificates.MethodCertificate;
import mobius.cct.classfile.Attribute;
import mobius.cct.constantpool.ConstantPoolBuilder;

/**
 * A method certificate wrapped in Attribute interface.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MethodCertificateAttribute implements Attribute {
  /**
   * Certificate.
   */
  private final MethodCertificate fCert;
  
  /**
   * Second constant pool.
   */
  private final ConstantPoolBuilder fSCP;
  
  /**
   * Constructor.
   * @param cert Certificate.
   * @param scp Second constant pool.
   */
  public MethodCertificateAttribute(final MethodCertificate cert,
                                    final ConstantPoolBuilder scp) {
    if ((cert == null) || (scp == null)) {
      throw new IllegalArgumentException();
    }
    fCert = cert;
    fSCP = scp;
  }

  /**
   * Get attribute name.
   * @return ClassCertificate.ATTR.
   */
  public String getName() {
    return MethodCertificate.ATTR;
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
    final byte[] data = fCert.getData();
    ds.writeInt(data.length);
    ds.write(data);
  }
}
