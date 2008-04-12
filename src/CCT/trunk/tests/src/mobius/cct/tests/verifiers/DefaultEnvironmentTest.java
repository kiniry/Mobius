package mobius.cct.tests.verifiers;

import java.util.Iterator;

import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.*;

import mobius.cct.certificates.Certificate;
import mobius.cct.certificates.DefaultCertificate;
import mobius.cct.repositories.ClassFile;
import mobius.cct.repositories.Repository;
import mobius.cct.tests.mocks.CyclicVerifier;
import mobius.cct.tests.mocks.MockClassFile;
import mobius.cct.tests.mocks.MockRepository;
import mobius.cct.util.Version;
import mobius.cct.verifiers.CyclicDependencyException;
import mobius.cct.verifiers.DefaultEnvironment;
import mobius.cct.verifiers.Environment;
import mobius.cct.verifiers.Verifier;

/**
 * Tests of default verification environment.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultEnvironmentTest { 
  /**
   * Repository used by tests.
   */
  private MockRepository fRepo;
  
  /**
   * Environment instance.
   */
  private DefaultEnvironment<ClassFile> fEnv;
  
  /**
   * Method called before each test.
   */
  @Before
  public void setUp() {
    fRepo = new MockRepository();
    
    fEnv = new DefaultEnvironment<ClassFile>(fRepo, false);
  }
  
  /**
   * Test empty environment.
   */
  @Test
  public void testEmpty() {
    Iterator<Verifier> i;
    i = fEnv.getVerifiers();
    assertNotNull(i);
    assertFalse(i.hasNext());
  }
  
  /**
   * Test verification of non-existing class.
   */
  @Test
  public void testNotFound() {
    try {
      assertFalse(fEnv.verify("", ""));
    } catch (CyclicDependencyException e) {
      fail("CyclicDependencyException");
    }
  }

  /**
   * Test null as first argument of verify().
   */
  @Test(expected=IllegalArgumentException.class)
  public void testVerifyNull1() throws Exception {
    fEnv.verify(null, "BML");
  }

  /**
   * Test null as second argument of verify().
   */
  @Test(expected=IllegalArgumentException.class)
  public void testVerifyNull2() throws Exception {
    fEnv.verify("/java/lang/Object", null);
  }
  
  /**
   * Test trusted classes mechanism.
   */
  @Test
  public void testTrustedClasses() {
    fEnv.addTrustedClass("/fake/class");
    fEnv.addTrustedClass("/another/fake/class");
    try {
      assertTrue(fEnv.verify("/fake/class", ""));
      assertTrue(fEnv.verify("/another/fake/class", ""));
      fEnv.removeTrustedClass("/fake/class");
      assertFalse(fEnv.verify("/fake/class", ""));
    } catch (CyclicDependencyException e) {
      fail("CyclicDependencyException");
    }
  }
  
  /**
   * Test cycle detection.
   */
  @Test
  public void testCycle() {
    Verifier<ClassFile> v = new CyclicVerifier();
    DefaultCertificate cert = 
      new DefaultCertificate(v.getCertificateType(), new Version(0, 5));
    MockClassFile c = new MockClassFile(
                                        new Certificate[]{cert}
    );
    fRepo.addClass("/mobius/cct/Test", c);
    fEnv.addVerifier(v);
    try {
      assertTrue(fEnv.verify("/mobius/cct/Test", "test"));
    } catch (CyclicDependencyException e) {
      fail("Cycle detected too early");
    }
  }
}
