package mobius.cct.repositories.classfile;

import java.io.OutputStream;
import java.io.IOException;
import java.util.Iterator;

import mobius.cct.certificates.Certificate;
import mobius.cct.repositories.InvalidCertificateException;

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
   * @return Iterator over vlass certificates.
   */
  Iterator<Certificate> getCertificates();
  
  /**
   * Set certificates of this class.
   * @param certs Class certificate.
   */
  void setCertificates(Certificate[] certs);  
}
