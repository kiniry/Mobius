package mobius.cct.tests.repositories;

import org.junit.Before;
import org.junit.Test;

import mobius.cct.repositories.ClasspathRepository;
import mobius.cct.repositories.DefaultClassFile;
import mobius.cct.repositories.DefaultClassReader;
import mobius.cct.repositories.DefaultRepository;
import mobius.cct.repositories.classpath.ClassPath;
import mobius.cct.repositories.classpath.DirEntry;

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
  private ClasspathRepository<DefaultClassFile> repo;
  
  /**
   * Method called before each test.
   */
  @Before
  public void setUp() {
    path = new ClassPath();
    path.addEntry(new DirEntry(testDir));
    repo = new ClasspathRepository<DefaultClassFile>(new DefaultClassReader(), path);
  }
  
  /**
   * Test loading of exisitng class.
   */
  @Test
  public void test1() throws Exception {
    repo.getClassFile("mobius.cct.testdata.Test9");
  }
  
  /**
   * Class not found.
   */
  @Test(expected=mobius.cct.repositories.NotFoundException.class)
  public void test2() throws Exception {
    repo.getClassFile("mobius.cct.testdata.FalseTest");
  }
}
