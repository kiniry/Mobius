package mobius.cct.tests.repositories;

import org.junit.Before;
import org.junit.Test;

import mobius.cct.repositories.DefaultClassFile;
import mobius.cct.repositories.DefaultClassReader;
import mobius.cct.repositories.DefaultRepository;

/**
 * Tests for class mobius.cct.repositories.DefaultRepository.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultRepositoryTest {
  /**
   * Repository instance.
   */
  private DefaultRepository<DefaultClassFile> fRepo;
  
  /**
   * Method called before each test.
   */
  @Before
  public void setUp() {
    fRepo = new DefaultRepository<DefaultClassFile>(new DefaultClassReader());
  }
  
  /**
   * Test loading of java.lang.Object.
   */
  @Test
  public void test1() throws Exception {
    fRepo.getClassFile("java.lang.Object");
  }
  
  /**
   * Class not found.
   */
  @Test(expected=mobius.cct.repositories.NotFoundException.class)
  public void test2() throws Exception {
    fRepo.getClassFile("mobius.cct.FaLsEClAsS");
  }
}
