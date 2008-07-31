package mobius.cct.tests.mocks;

import java.io.IOException;
import java.util.HashMap;

import mobius.cct.classfile.ClassName;
import mobius.cct.repositories.NotFoundException;
import mobius.cct.repositories.Repository;

/**
 * Repository implementation used for testing.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockRepository implements Repository<MockClassFile> {
  /**
   * Class files in repository.
   */
  private HashMap<String, MockClassFile> fClasses;
  /**
   * Certificate files in repository.
   */
  private HashMap<String, MockClassFile> fCerts;
  
  /**
   * Constructor - create empty repository.
   */
  public MockRepository() {
    fClasses = new HashMap<String, MockClassFile>();
    fCerts   = new HashMap<String, MockClassFile>();
  }
  
  /**
   * Add class file to repository.
   * @param name Class name.
   * @param file ClassFile object.
   */
  public void addClass(String name, MockClassFile file) {
    fClasses.put(name, file);
  }
  
  /**
   * Add certificate file to repository.
   * @param name Class name.
   * @param file ClassFile object.
   */
  public void addCert(String name, MockClassFile file) {
    fCerts.put(name, file);
  }
  
  @Override
  public MockClassFile getCertFile(ClassName name) throws IOException {
    return fCerts.get(name.internalForm());
  }

  @Override
  public MockClassFile getClassFile(ClassName name) 
    throws NotFoundException, IOException {
    final MockClassFile result = fClasses.get(name.internalForm());
    if (result == null) {
      throw new NotFoundException();
    } else {
      return result;
    }
  }

}
