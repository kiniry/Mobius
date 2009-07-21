package mobius.cct.tests.repositories;

import mobius.cct.classfile.ClassName;
import mobius.cct.repositories.ClasspathRepository;
import mobius.cct.repositories.classpath.ClassPath;
import mobius.cct.repositories.classpath.DirEntry;
import mobius.cct.tests.mocks.MockClassReader;
import mobius.cct.tests.mocks.MockRepoClass;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests for class mobius.cct.repositories.DefaultRepository.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ClasspathRepositoryTest {
  /**
   * Directory with test classes.
   */
  private static final String testDir = "./tests/data";
  
  /**
   * Classpath instance.
   */
  private ClassPath path;
  
  /**
   * Repository instance.
   */
  private ClasspathRepository<MockRepoClass> repo;
  
  /**
   * Method called before each test.
   */
  @Before
  public void setUp() {
    path = new ClassPath();
    path.addEntry(new DirEntry(testDir));
    repo = new ClasspathRepository<MockRepoClass>(new MockClassReader(), path);
  }
  
  /**
   * Test loading of existing class.
   */
  @Test
  public void test1() throws Exception {
    repo.getClassFile(ClassName.parseInternal(
      "mobius/cct/testdata/Test7"
    ));
  }
  
  /**
   * Class not found.
   */
  @Test(expected=mobius.cct.repositories.NotFoundException.class)
  public void test2() throws Exception {
    repo.getClassFile(ClassName.parseInternal(
      "mobius/cct/testdata/FalseTest"
    ));
  }
}
