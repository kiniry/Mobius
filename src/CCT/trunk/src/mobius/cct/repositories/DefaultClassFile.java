package mobius.cct.repositories;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Iterator;

import mobius.cct.certificates.Certificate;

/**
 * Default implementation of class file. No external 
 * libraries (bcel, asm, ...) are used.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultClassFile implements ClassFile {
  /**
   * Constructor - read class from input stream.
   * @param is Input stream.
   * @throws IOException if the file cannot be parsed. If its format is invalid,
   *    InvalidFormatException should be thrown.
   */
  public DefaultClassFile(final InputStream is) {
  }
  
  /**
   * Write class file to given output stream.
   * @param os output stream.
   * @throws IOException if it is thrown during writing to the stream.
   * @throws InvalidCertificateException if the certificate does not match class.
   */
  @Override
  public void write(final OutputStream os) 
    throws IOException, InvalidCertificateException {
  }
  
  /**
   * Get certificate of this class.
   * @return Class certificate.
   */
  @Override
  public Iterator<Certificate> getCertificates() {
    return null;
  }
  
  /**
   * Set certificates of this class.
   * @param certs Class certificates.
   */
  public void setCertificates(final Certificate[] certs) {
  }
}
