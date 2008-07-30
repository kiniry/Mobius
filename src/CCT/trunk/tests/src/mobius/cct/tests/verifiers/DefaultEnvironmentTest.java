package mobius.cct.tests.verifiers;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Iterator;
import java.util.LinkedList;

import mobius.cct.certificates.CertificatePack;
import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.repositories.classfile.ClassName;
import mobius.cct.tests.mocks.CyclicVerifier;
import mobius.cct.tests.mocks.MockCertificateParser;
import mobius.cct.tests.mocks.MockClassFile;
import mobius.cct.tests.mocks.MockRepository;
import mobius.cct.util.Version;
import mobius.cct.verifiers.CyclicDependencyException;
import mobius.cct.verifiers.DefaultEnvironment;
import mobius.cct.verifiers.Verifier;

import org.junit.Before;
import org.junit.Test;

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
  private DefaultEnvironment<MockClassFile> fEnv;
  
  /**
   * Method called before each test.
   */
  @Before
  public void setUp() {
    fRepo = new MockRepository();
    
    fEnv = new DefaultEnvironment<MockClassFile>(fRepo, false);
  }
  
  /**
   * Test empty environment.
   */
  @Test
  public void testEmpty() {
    Iterator<Verifier<MockClassFile>> i;
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
    Verifier<MockClassFile> v = new CyclicVerifier();
    ClassCertificate cert = 
      new ClassCertificate("mobius.cct.testcert",
                           new Version(0, 5),
                           new String[]{},
                           new byte[]{});
    CertificatePack certs = 
      new CertificatePack(cert, 
                          new LinkedList<MethodCertificate>());
    MockClassFile c = 
      new MockClassFile(
        ClassName.parseInternal("testpackage/TestClass"),
        new CertificatePack[]{certs});
    fRepo.addClass("/mobius/cct/Test", c);
    fEnv.setCertificateParser(new MockCertificateParser());
    fEnv.addVerifier(v);
    try {
      assertTrue(fEnv.verify("/mobius/cct/Test", "test"));
    } catch (CyclicDependencyException e) {
      fail("Cycle detected too early");
    }
  }
}
