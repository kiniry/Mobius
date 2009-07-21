package mobius.cct.tests.repositories;

import mobius.cct.classfile.ClassName;
import mobius.cct.repositories.DefaultRepository;
import mobius.cct.tests.mocks.MockClassReader;
import mobius.cct.tests.mocks.MockRepoClass;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests for class mobius.cct.repositories.DefaultRepository.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultRepositoryTest {
  /**
   * Repository instance.
   */
  private DefaultRepository<MockRepoClass> fRepo;
  
  /**
   * Method called before each test.
   */
  @Before
  public void setUp() {
    fRepo = 
      new DefaultRepository<MockRepoClass>(new MockClassReader());
  }
  
  /**
   * Test loading of java.lang.Object.
   */
  @Test
  public void test1() throws Exception {
    fRepo.getClassFile(ClassName.parseInternal("java/lang/Object"));
  }
  
  /**
   * Class not found.
   */
  @Test(expected=mobius.cct.repositories.NotFoundException.class)
  public void test2() throws Exception {
    fRepo.getClassFile(ClassName.parseInternal("mobius/cct/FaLsEClAsS"));
  }
}
