package mobius.cct.repositories;

import java.io.OutputStream;
import java.io.IOException;
import mobius.cct.certificates.Certificate;

/**
 * This interface contains methods common to all
 * implementations of class file.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface ClassFile {
  /**
   * Write class file to given output stream.
   * @param os output stream.
   * @throws IOException if it is thrown during writing to the stream.
   * @throws InvalidCertificateException if the certificate does not match class.
   */
  void write(OutputStream os) 
    throws IOException, InvalidCertificateException;
  
  /**
   * Get certificates of this class.
   * @return Class certificates.
   */
  Certificate[] getCertificates();
  
  /**
   * Get certificate of this class.
   * @param certs Class certificate.
   */
  void setCertificates(Certificate[] certs);  
}
