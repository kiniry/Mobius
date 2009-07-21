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
public class MockRepository implements Repository<MockRepoClass> {
  /**
   * Class files in repository.
   */
  private HashMap<String, MockRepoClass> fClasses;
  /**
   * Certificate files in repository.
   */
  private HashMap<String, MockRepoClass> fCerts;
  
  /**
   * Constructor - create empty repository.
   */
  public MockRepository() {
    fClasses = new HashMap<String, MockRepoClass>();
    fCerts   = new HashMap<String, MockRepoClass>();
  }
  
  /**
   * Add class file to repository.
   * @param name Class name.
   * @param file ClassFile object.
   */
  public void addClass(String name, MockRepoClass file) {
    fClasses.put(name, file);
  }
  
  /**
   * Add certificate file to repository.
   * @param name Class name.
   * @param file ClassFile object.
   */
  public void addCert(String name, MockRepoClass file) {
    fCerts.put(name, file);
  }
  
  public MockRepoClass getCertFile(ClassName name) throws IOException {
    return fCerts.get(name.internalForm());
  }

  public MockRepoClass getClassFile(ClassName name) 
    throws NotFoundException, IOException {
    final MockRepoClass result = fClasses.get(name.internalForm());
    if (result == null) {
      throw new NotFoundException(name);
    } else {
      return result;
    }
  }

}
