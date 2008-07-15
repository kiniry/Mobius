package mobius.cct.tests.mocks;

import java.util.Iterator;

import mobius.cct.certificates.Certificate;
import mobius.cct.repositories.classfile.Attribute;
import mobius.cct.repositories.classfile.ClassFile;
import mobius.cct.repositories.classfile.MethodName;

/**
 * Mock class file used for testing.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockClassFile implements ClassFile {
  /**
   * Certificates.
   */
  private final Certificate[] fCerts;
  
  public Certificate[] getCerts() {
    return fCerts;
  }

  /**
   * Constructor - create file with no certificates.
   */
  public MockClassFile(){
    fCerts = new Certificate[]{};
  }
  
  /**
   * Constructor - create class file with given set of
   * certificates.
   * @param certs Certificates.
   */
  public MockClassFile(final Certificate[] certs) {
    fCerts = certs;
  }
  
  @Override
  public Iterator<Attribute> classAttributes() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Iterator<Attribute> methodAttribute(MethodName m) {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * Return all methods of this class.
   * @return Iterator.
   */
  public Iterator<MethodName> getMethods() {
    //TODO
    // Currently not used. Should scan all certificates and
    // return all found methods.
    return null;
  }
  
}
