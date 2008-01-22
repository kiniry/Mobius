package mobius.cct.tests.certificates;

import static org.junit.Assert.*;

import java.util.Iterator;

import org.junit.Before;
import org.junit.Test;
import mobius.cct.certificates.DefaultCertificate;

/**
 * Tests for class mobius.cct.certificates.DefaultCertificate.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultCertificateTest {
  /**
   * Certificate instance, recreated before each test.
   */
  private DefaultCertificate fCert;
  
  /**
   * Major version of fCert.
   */
  private static final byte MAJOR = 42;
  
  /**
   * Minor version of fCert.
   */
  private static final byte MINOR = 4;
  
  /**
   * Type of fCert.
   */
  private static final String TYPE = "mobius.testCert";
  
  /**
   * Certificate content.
   */
  private static final byte[] SAMPLE1 = new byte[]{1,2,3,4};
  
  /**
   * Certificate content.
   */
  private static final byte[] SAMPLE2 = new byte[]{1,2,3,4};  

  /**
   * Method executed before each test.
   */
  @Before
  public void setUp() {
    fCert = new DefaultCertificate(TYPE, MAJOR, MINOR);
  }
  
  /**
   * Test constructor - should create empty cert with
   * correct type and version.
   */
  @Test
  public void testConstructor() {
    assertEquals(TYPE, fCert.getType());
    assertEquals(MAJOR, fCert.getMajorVersion());
    assertEquals(MINOR, fCert.getMinorVersion());
    assertNotNull(fCert.getCertifiedMethods());
    assertFalse(fCert.getCertifiedMethods().hasNext());
    assertNotNull(fCert.getImportedCerts());
    assertTrue(fCert.getImportedCerts().isEmpty());
    assertNotNull(fCert.getClassCertificate());
    assertEquals(0, fCert.getClassCertificate().length);
  }
  
  /**
   * Test class certificate setter - null argument.
   */
  @Test(expected=IllegalArgumentException.class)
  public void testSetClassCertificate1() {
    fCert.setClassCertificate(null);
  }

  /**
   * Test class certificate setter - valid argument.
   */
  @Test
  public void testSetClassCertificate2() {
    fCert.setClassCertificate(SAMPLE1);
    assertArrayEquals(SAMPLE1, fCert.getClassCertificate());
    fCert.setClassCertificate(SAMPLE2);
    assertArrayEquals(SAMPLE2, fCert.getClassCertificate());
  }
  
  /**
   * Test getCertifiedMethods - redefined certificate.
   */
  @Test
  public void testGetCertifiedMethods() {
    Iterator<String> i;
    
    fCert.addMethodCert("", SAMPLE1);
    fCert.addMethodCert("", SAMPLE2);
    i = fCert.getCertifiedMethods();
    assertNotNull(i);
    assertTrue(i.hasNext());
    assertEquals(i.next(), "");
    assertFalse(i.hasNext());
  }
  
  /**
   * Test addMethodCert - null as first argument.
   */
  @Test(expected=IllegalArgumentException.class)
  public void testAddMethodCert1() {
    fCert.addMethodCert(null, SAMPLE1);
  }

  /**
   * Test addMethodCert - null as second argument.
   */
  @Test(expected=IllegalArgumentException.class)
  public void testAddMethodCert2() {
    fCert.addMethodCert("", null);
  }

  /**
   * Test addMethodCert - valid arguments.
   */
  @Test
  public void testAddMethodCert3() {
    fCert.addMethodCert("", SAMPLE1);
    assertArrayEquals(SAMPLE1, fCert.getMethodCertificate(""));
  }
  
  /**
   * Test addMethodCert - certificate redefined.
   */
  @Test
  public void testAddMethodCert4() {
    fCert.addMethodCert("", SAMPLE1);
    fCert.addMethodCert("", SAMPLE2);
    assertArrayEquals(SAMPLE1, fCert.getMethodCertificate(""));
  }
  
  /**
   * Test removeMethodCert - null argument.
   */
  @Test(expected=IllegalArgumentException.class)
  public void testRemoveMethodCert1() {
    fCert.removeMethodCert(null);
  }

  /**
   * Test removeMethodCert - valid argument, nothing to remove.
   */
  @Test
  public void testRemoveMethodCert2() {
    fCert.removeMethodCert("");
  }

  /**
   * Test removeMethodCert - valid argument, 
   * certificate present.
   */
  @Test
  public void testRemoveMethodCert3() {
    fCert.addMethodCert("", SAMPLE1);
    fCert.removeMethodCert("");
    assertNotNull(fCert.getCertifiedMethods());
    assertFalse(fCert.getCertifiedMethods().hasNext());
  }
  
}
