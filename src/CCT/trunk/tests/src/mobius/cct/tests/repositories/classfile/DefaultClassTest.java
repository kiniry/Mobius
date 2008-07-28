package mobius.cct.tests.repositories.classfile;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Iterator;

import mobius.cct.certificates.Certificate;
import mobius.cct.certificates.CertificateParser;
import mobius.cct.certificates.CertifiedMutableClass;
import mobius.cct.certificates.DefaultCertificateParser;
import mobius.cct.repositories.classfile.DefaultClassFile;
import mobius.cct.repositories.classfile.DefaultClassReader;
import mobius.cct.repositories.classfile.MethodName;
import mobius.cct.tests.testutil.Util;
import mobius.cct.util.Version;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests for default implementations of class file handling.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultClassTest {
  /**
   * Direcotry with test classes.
   */
  private static final String testDir = "./tests/data";
  
  /**
   * DefaultClassReader instance.
   */
  private DefaultClassReader fReader;
  
  /**
   * Certificate parser.
   */
  private CertificateParser<DefaultClassFile> fParser;
  
  /**
   * Method called before each test.
   */
  @Before
  public void setUp() {
    fReader = new DefaultClassReader();
    fParser = new DefaultCertificateParser<DefaultClassFile>();
  }
  
  /**
   * Test class reading without parsing certificates.
   */
  @Test
  public void testRead() throws IOException {
    FileInputStream is = 
      new FileInputStream(testDir+"/mobius/cct/testdata/Test9.class");
    DefaultClassFile f = fReader.read(is);
    
    assertEquals(1, f.getClassAttrCount("mobius.PCCCert"));
    assertEquals(1, f.getClassAttrCount("org.bmlspecs.SecondConstantPool"));
    assertEquals(new Version(50, 0), f.getVersion());
    MethodName m = MethodName.get("<init>", "()V");
    assertEquals(1, f.getMethodAttrCount(m, "mobius.PCCCert"));
    // TODO: more tests...
  }
  
  /**
   * Simple class with no certificates and no second constant pool.
   */
  @Test
  public void testNoCertificate1() throws Exception {
    CertifiedMutableClass<DefaultClassFile> f = 
      read("mobius/cct/testdata/Test1");
    assertNotNull(f);
    Iterator<Certificate> i = f.getCertificates();
    assertNotNull(i);
    assertFalse(i.hasNext());
  }
  
  /**
   * Simple class with second constant pool, but no certificates.
   */
  @Test
  public void testNoCertificate2() throws Exception {
    CertifiedMutableClass<DefaultClassFile> f = 
      read("mobius/cct/testdata/Test2");
    assertNotNull(f);
    Iterator<Certificate> i = f.getCertificates();
    assertNotNull(i);
    assertFalse(i.hasNext());
  }  
  
  /**
   * Class with one certificate, but no second constant pool.
   * Such class file is of course invalid.
   */
  @Test(expected=mobius.cct.repositories.InvalidFormatException.class)
  public void testInvalid1() throws Exception {
    read("mobius/cct/testdata/Test3");
  }
  
  /**
   * Simple class with second constant pool, but no class-level certificate.
   * Method certificates are present but should NOT be found.
   */
  @Test
  public void testNoCertificate3() throws Exception {
    CertifiedMutableClass<DefaultClassFile> f = 
      read("mobius/cct/testdata/Test4");
    assertNotNull(f);
    Iterator<Certificate> i = f.getCertificates();
    assertNotNull(i);
    assertFalse(i.hasNext());
  }  
  
  /**
   * Class with invalid SCP index in certificate.
   */
  @Test(expected=mobius.cct.repositories.InvalidFormatException.class)
  public void testInvalid2() throws Exception {
    read("mobius/cct/testdata/Test5");
  }

  /**
   * Class with unusable SCP index in certificate.
   */
  @Test(expected=mobius.cct.repositories.InvalidFormatException.class)
  public void testInvalid3() throws Exception {
    read("mobius/cct/testdata/Test6");
  }

  /**
   * Class with wrong constant type in SCP.
   */
  @Test(expected=mobius.cct.repositories.InvalidFormatException.class)
  public void testInvalid4() throws Exception {
    read("mobius/cct/testdata/Test7");
  }

  /**
   * Class with invalid certificate length.
   */
  @Test(expected=mobius.cct.repositories.InvalidFormatException.class)
  public void testInvalid5() throws Exception {
    read("mobius/cct/testdata/Test8");
  }

  /**
   * Class not found.
   */
  @Test(expected=java.io.FileNotFoundException.class)
  public void testNotFound() throws Exception {
    read("mobius/cct/testdata/FalseTest");
  }
  
  /**
   * Class with one class-level certificate and one method-level certificate.
   */
  @Test
  public void testRead1() throws Exception {
    CertifiedMutableClass<DefaultClassFile> f = 
      read("mobius/cct/testdata/Test9");
    assertNotNull(f);
    Iterator<Certificate> i = f.getCertificates();
    assertNotNull(i);
    assertTrue(i.hasNext());
    Certificate cert = i.next();
    assertFalse(i.hasNext());
    assertEquals("mobius.testcert", cert.getType());
    assertEquals(new Version(1, 0), cert.getVersion());
    Iterator<String> it = cert.getCertifiedMethods();
    assertTrue(it.hasNext());
    it.next();
    assertFalse(it.hasNext());
  }
  
  /**
   * Test class writing.
   */
  @Test
  public void testWrite1() throws Exception {
    CertifiedMutableClass<DefaultClassFile> f = 
      read("mobius/cct/testdata/Test1");
    assertNotNull(f);
    ByteArrayOutputStream os = new ByteArrayOutputStream();
    f.writeTo(os);
    ByteArrayInputStream is = new ByteArrayInputStream(os.toByteArray());
    //assertEquals("12872b2fb305213f2c7adac2a945f3da", 
    //             Util.toHex(Util.digest(is, Util.MD5)));
    // Useless -- order of attributes may change.
    //TODO: re-read written class.
  }

  /**
   * Another class writing test.
   */
  @Test
  public void testWrite2() throws Exception {
    CertifiedMutableClass<DefaultClassFile> f = 
      read("mobius/cct/testdata/Test9");
    assertNotNull(f);
    ByteArrayOutputStream os = new ByteArrayOutputStream();
    f.writeTo(os);
    ByteArrayInputStream is = new ByteArrayInputStream(os.toByteArray());
    //assertEquals("ee9706019896636e12b7ee1f40d13b7e", 
    //             Util.toHex(Util.digest(is, Util.MD5)));
    // Useless -- order of attributes may change.
    //TODO: re-read written class.
  }
  
  /**
   * Read a class.
   * @param name Class name.
   */
  private CertifiedMutableClass<DefaultClassFile> 
  read(final String name) throws Exception {
    FileInputStream is = new FileInputStream(testDir+"/"+name+".class");
    DefaultClassFile f = fReader.read(is);
    return new CertifiedMutableClass<DefaultClassFile>(fParser.parse(f));
  }
}
