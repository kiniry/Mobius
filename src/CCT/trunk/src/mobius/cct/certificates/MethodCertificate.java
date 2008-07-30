package mobius.cct.certificates;

import mobius.cct.classfile.MethodName;
import mobius.cct.util.Version;

/**
 * Method certificate.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MethodCertificate extends Certificate {
  /**
   * Attribute name.
   */
  public static final String ATTR = "mobius.PCCMethodCert";
  /**
   * Method name.
   */
  private final MethodName fMethod;
  
  /**
   * Constructor.
   * @param method Method name.
   * @param type Certificate type.
   * @param version Certificate version.
   * @param data Certificate data.
   */
  public MethodCertificate(final MethodName method,
                           final String type,
                           final Version version,
                           final byte[] data) {
    super(type, version, data);
    fMethod = method;
  }
  
  /**
   * Merge with another method certificate.
   * Data sections are concatenated.
   * @param c Method certificate.
   * @return Merged certificate.
   */
  public MethodCertificate merge(final MethodCertificate c) {
    final byte[] data1 = getData();
    final byte[] data2 = c.getData();
    final byte[] data = 
      new byte[data1.length + data2.length];
    for (int i = 0; i < data1.length; i++) {
      data[i] = data1[i];
    }
    for (int i = 0; i < data2.length; i++) {
      data[data1.length + i] = data2[i];
    }
    return 
      new MethodCertificate(fMethod, getType(), 
                            getVersion(), data);
  }
  
  /**
   * Get method name.
   * @return Method name.
   */
  public MethodName getMethod() {
    return fMethod;
  }

}
