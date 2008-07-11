package mobius.cct.tests.mocks;

import java.io.IOException;
import java.util.HashMap;

import mobius.cct.repositories.InvalidCertificateException;
import mobius.cct.repositories.NotFoundException;
import mobius.cct.repositories.Repository;
import mobius.cct.repositories.classfile.ClassFile;

/**
 * Repository implmentation used for testing.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockRepository implements Repository<ClassFile> {
  /**
   * Class files in repository.
   */
  private HashMap<String, ClassFile> fClasses;
  /**
   * Certificate files in repository.
   */
  private HashMap<String, ClassFile> fCerts;
  
  /**
   * Constructor - create empty repository.
   */
  public MockRepository() {
    fClasses = new HashMap<String, ClassFile>();
    fCerts   = new HashMap<String, ClassFile>();
  }
  
  /**
   * Add class file to repository.
   * @param name Class name.
   * @param file ClassFile object.
   */
  public void addClass(String name, ClassFile file) {
    fClasses.put(name, file);
  }
  
  /**
   * Add certificate file to repository.
   * @param name Class name.
   * @param file ClassFile object.
   */
  public void addCert(String name, ClassFile file) {
    fCerts.put(name, file);
  }
  
  @Override
  public ClassFile getCertFile(String name) throws IOException,
      InvalidCertificateException {
    return fCerts.get(name);
  }

  @Override
  public ClassFile getClassFile(String name) throws NotFoundException,
      IOException, InvalidCertificateException {
    return fClasses.get(name);
  }

}
