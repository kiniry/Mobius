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
import mobius.cct.classfile.ClassName;
import mobius.cct.tests.mocks.CyclicVerifier;
import mobius.cct.tests.mocks.MockCertificateParser;
import mobius.cct.tests.mocks.MockRepoClass;
import mobius.cct.tests.mocks.MockRepository;
import mobius.cct.util.Version;
import mobius.cct.verifiers.DefaultEnvironment;
import mobius.cct.verifiers.VerificationException;
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
  private DefaultEnvironment<MockRepoClass> fEnv;
  
  /**
   * Method called before each test.
   */
  @Before
  public void setUp() {
    fRepo = new MockRepository();
    
    fEnv = new DefaultEnvironment<MockRepoClass>(fRepo);
  }
  
  /**
   * Test empty environment.
   */
  @Test
  public void testEmpty() {
    Iterator<Verifier<MockRepoClass>> i;
    i = fEnv.getVerifiers();
    assertNotNull(i);
    assertFalse(i.hasNext());
  }
  
  /**
   * Test verification of non-existing class.
   */
  @Test(expected=VerificationException.class)
  public void testNotFound() throws Exception {
    fEnv.verify(ClassName.parseInternal("X"), "");
  }

  /**
   * Test verification of empty array of classes.
   */
  @Test
  public void testEmptyArray() throws Exception {
    assertTrue(fEnv.verify(new ClassName[0], new String[0]));
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
    fEnv.verify(ClassName.parseInternal("/java/lang/Object"), null);
  }
  
  /**
   * Test trusted classes mechanism.
   */
  @Test
  public void testTrustedClasses() {
    final ClassName fk = ClassName.parseInternal("/fake/Class");
    final ClassName afk = ClassName.parseInternal("/another/fake/Class");
    fEnv.addTrustedClass(fk);
    fEnv.addTrustedClass(afk);
    try {
      assertTrue(fEnv.verify(fk, ""));
      assertTrue(fEnv.verify(afk, ""));
      fEnv.removeTrustedClass(fk);
      fEnv.verify(fk, "");
    } catch (VerificationException e) {
      return;
    }
    fail("VerificationException not thrown.");
  }
  
  /**
   * Test cycle detection.
   */
  @Test
  public void testCycle() {
    Verifier<MockRepoClass> v = new CyclicVerifier();
    ClassCertificate cert = 
      new ClassCertificate(v.getCertificateType(),
                           new Version(0, 5),
                           new String[]{},
                           new byte[]{});
    CertificatePack certs = 
      new CertificatePack(cert, 
                          new LinkedList<MethodCertificate>());
    MockRepoClass c = 
      new MockRepoClass(
        ClassName.parseInternal("mobius/cct/Test"),
        new CertificatePack[]{certs});
    fRepo.addClass("mobius/cct/Test", c);
    fEnv.setCertificateParser(new MockCertificateParser());
    fEnv.addVerifier(v);
    try {
      assertTrue(fEnv.verify(
         ClassName.parseInternal("mobius/cct/Test"), 
         v.getSpecificationType())
      );
    } catch (VerificationException e) {
      fail("VerificationException: " + e.toString());
    }
  }
}
