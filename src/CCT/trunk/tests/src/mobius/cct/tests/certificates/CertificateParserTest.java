package mobius.cct.tests.certificates;

import java.util.ArrayList;
import java.util.List;

import mobius.cct.certificates.Certificate;
import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.DefaultCertificateParser;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.classfile.Attribute;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.DefaultAttribute;
import mobius.cct.classfile.MethodName;
import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.tests.mocks.MockCertVisitor;
import mobius.cct.tests.mocks.MockClassFile;
import mobius.cct.util.Version;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests of default certificate parser.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CertificateParserTest {
  /**
   * Certificate parser.
   */
  private DefaultCertificateParser<MockClassFile> fParser;
  
  /**
   * Method executed before each test.
   */
  @Before
  public void setUp() {
    fParser = new DefaultCertificateParser<MockClassFile>();
  }
  
  
  /**
   * Class with no certificates and no SCP.
   */
  @Test
  public void testClass1() throws Exception {
    final MockClassFile f = makeTest1();
    final List<Certificate> certs = new ArrayList<Certificate>();
    final MockCertVisitor v = new MockCertVisitor(certs);
    fParser.parse(f, v);
  }
  
  /**
   * Class with a SCP but no certificates.
   */
  @Test
  public void testClass2() throws Exception {
    final MockClassFile f = makeTest2();
    final List<Certificate> certs = new ArrayList<Certificate>();
    final MockCertVisitor v = new MockCertVisitor(certs);
    fParser.parse(f, v);
  }
  
  /**
   * Class with a certificate, but no SCP.
   */
  @Test(expected=InvalidFormatException.class)
  public void testClass3() throws Exception {
    final MockClassFile f = makeTest3();
    final List<Certificate> certs = new ArrayList<Certificate>();
    final MockCertVisitor v = new MockCertVisitor(certs);
    fParser.parse(f, v);
  }
  
  /**
   * Class with method certificates, but no class certificate.
   * This is invalid - class level certificate MUST be present.
   */
  @Test(expected=InvalidFormatException.class)
  public void testClass4() throws Exception {
    final MockClassFile f = makeTest4();
    final List<Certificate> certs = new ArrayList<Certificate>();
    certs.add(new MethodCertificate(
      MethodName.get("<init>", "()V"),
      "mobius.testcert",
      new Version(1, 0),
      "Test certificate content".getBytes()
    ));
    final MockCertVisitor v = new MockCertVisitor(certs);
    fParser.parse(f, v);
  }
  
  /**
   * Class with invalid SCP index.
   */
  @Test(expected=InvalidFormatException.class)
  public void testClass5() throws Exception {
    final MockClassFile f = makeTest5();
    final List<Certificate> certs = new ArrayList<Certificate>();
    final MockCertVisitor v = new MockCertVisitor(certs);
    fParser.parse(f, v);
  }
  
  /**
   * Class with unusable SCP index.
   */
  @Test(expected=InvalidFormatException.class)
  public void testClass6() throws Exception {
    final MockClassFile f = makeTest6();
    final List<Certificate> certs = new ArrayList<Certificate>();
    final MockCertVisitor v = new MockCertVisitor(certs);
    fParser.parse(f, v);
  }
  
  /**
   * Class with invalid constant type in SCP.
   */
  @Test(expected=InvalidFormatException.class)
  public void testClass7() throws Exception {
    final MockClassFile f = makeTest7();
    final List<Certificate> certs = new ArrayList<Certificate>();
    final MockCertVisitor v = new MockCertVisitor(certs);
    fParser.parse(f, v);
  }
  
  /**
   * Class with invalid certificate length.
   */
  @Test(expected=InvalidFormatException.class)
  public void testClass8() throws Exception {
    final MockClassFile f = makeTest8();
    final List<Certificate> certs = new ArrayList<Certificate>();
    final MockCertVisitor v = new MockCertVisitor(certs);
    fParser.parse(f, v);
  }
  
  /**
   * Class with class and method certificate.
   */
  @Test
  public void testClass9() throws Exception {
    final MockClassFile f = makeTest9();
    final List<Certificate> certs = new ArrayList<Certificate>();
    certs.add(new MethodCertificate(
      MethodName.get("<init>", "()V"),
      "mobius.testcert",
      new Version(1, 0),
      "Test certificate content".getBytes()
    ));
    certs.add(new ClassCertificate(
      "mobius.testcert",
      new Version(1, 0),
      new String[]{},
      "Test certificate content".getBytes()
    ));
    final MockCertVisitor v = new MockCertVisitor(certs);
    fParser.parse(f, v);
  }
  
  ////////////////////////////////////////////////////
  // Generated from class files (using BCEL).
  ////////////////////////////////////////////////////  
  private MockClassFile makeTest1() {
    final MockClassFile result = new MockClassFile(ClassName.parseInternal("mobius.cct.testdata.Test1"));
    final MethodName m0 = MethodName.get("<init>", "()V");
    final String m0attr0type = "Code";
    final byte[] m0data0 = new byte[]{0, 0, 0, 1, 0, 0, 0, 5, 42, -73, 0, 8, -79, 0, 0, 0, 0};
    final Attribute m0attr0 = new DefaultAttribute(m0attr0type, m0data0);
    result.addAttribute(m0, m0attr0);
    return result;
  }
  private MockClassFile makeTest2() {
    final MockClassFile result = new MockClassFile(ClassName.parseInternal("mobius.cct.testdata.Test2"));
    final String cattr0type = "org.bmlspecs.SecondConstantPool";
    final byte[] cdata0 = new byte[]{0, 1, 0, 1, 0, 16, 84, 101, 115, 116, 84, 101, 115, 116, 84, 101, 115, 116, 84, 101, 115, 116};
    final Attribute cattr0 = new DefaultAttribute(cattr0type, cdata0);
    result.addAttribute(cattr0);
    final MethodName m0 = MethodName.get("<init>", "()V");
    final String m0attr0type = "Code";
    final byte[] m0data0 = new byte[]{0, 0, 0, 1, 0, 0, 0, 5, 42, -73, 0, 8, -79, 0, 0, 0, 0};
    final Attribute m0attr0 = new DefaultAttribute(m0attr0type, m0data0);
    result.addAttribute(m0, m0attr0);
    return result;
  }
  private MockClassFile makeTest3() {
    final MockClassFile result = new MockClassFile(ClassName.parseInternal("mobius.cct.testdata.Test3"));
    final String cattr0type = "mobius.PCCCert";
    final byte[] cdata0 = new byte[]{0, 1, 1, 0, 0, 0, 0, 0, 0, 24, 84, 101, 115, 116, 32, 99, 101, 114, 116, 105, 102, 105, 99, 97, 116, 101, 32, 99, 111, 110, 116, 101, 110, 116};
    final Attribute cattr0 = new DefaultAttribute(cattr0type, cdata0);
    result.addAttribute(cattr0);
    final MethodName m0 = MethodName.get("<init>", "()V");
    final String m0attr0type = "Code";
    final byte[] m0data0 = new byte[]{0, 0, 0, 1, 0, 0, 0, 5, 42, -73, 0, 8, -79, 0, 0, 0, 0};
    final Attribute m0attr0 = new DefaultAttribute(m0attr0type, m0data0);
    result.addAttribute(m0, m0attr0);
    return result;
  }
  private MockClassFile makeTest4() {
    final MockClassFile result = new MockClassFile(ClassName.parseInternal("mobius.cct.testdata.Test4"));
    final String cattr0type = "org.bmlspecs.SecondConstantPool";
    final byte[] cdata0 = new byte[]{0, 1, 0, 1, 0, 15, 109, 111, 98, 105, 117, 115, 46, 116, 101, 115, 116, 99, 101, 114, 116};
    final Attribute cattr0 = new DefaultAttribute(cattr0type, cdata0);
    result.addAttribute(cattr0);
    final MethodName m0 = MethodName.get("<init>", "()V");
    final String m0attr0type = "Code";
    final byte[] m0data0 = new byte[]{0, 0, 0, 1, 0, 0, 0, 5, 42, -73, 0, 8, -79, 0, 0, 0, 0};
    final Attribute m0attr0 = new DefaultAttribute(m0attr0type, m0data0);
    result.addAttribute(m0, m0attr0);
    final String m0attr1type = "mobius.PCCMethodCert";
    final byte[] m0data1 = new byte[]{0, 1, 1, 0, 0, 0, 0, 24, 84, 101, 115, 116, 32, 99, 101, 114, 116, 105, 102, 105, 99, 97, 116, 101, 32, 99, 111, 110, 116, 101, 110, 116};
    final Attribute m0attr1 = new DefaultAttribute(m0attr1type, m0data1);
    result.addAttribute(m0, m0attr1);
    return result;
  }
  private MockClassFile makeTest5() {
    final MockClassFile result = new MockClassFile(ClassName.parseInternal("mobius.cct.testdata.Test5"));
    final String cattr0type = "mobius.PCCCert";
    final byte[] cdata0 = new byte[]{0, 42, 1, 0, 0, 0, 0, 0, 0, 24, 84, 101, 115, 116, 32, 99, 101, 114, 116, 105, 102, 105, 99, 97, 116, 101, 32, 99, 111, 110, 116, 101, 110, 116};
    final Attribute cattr0 = new DefaultAttribute(cattr0type, cdata0);
    result.addAttribute(cattr0);
    final String cattr1type = "org.bmlspecs.SecondConstantPool";
    final byte[] cdata1 = new byte[]{0, 1, 0, 1, 0, 15, 109, 111, 98, 105, 117, 115, 46, 116, 101, 115, 116, 99, 101, 114, 116};
    final Attribute cattr1 = new DefaultAttribute(cattr1type, cdata1);
    result.addAttribute(cattr1);
    final MethodName m0 = MethodName.get("<init>", "()V");
    final String m0attr0type = "Code";
    final byte[] m0data0 = new byte[]{0, 0, 0, 1, 0, 0, 0, 5, 42, -73, 0, 8, -79, 0, 0, 0, 0};
    final Attribute m0attr0 = new DefaultAttribute(m0attr0type, m0data0);
    result.addAttribute(m0, m0attr0);
    return result;
  }
  private MockClassFile makeTest6() {
    final MockClassFile result = new MockClassFile(ClassName.parseInternal("mobius.cct.testdata.Test6"));
    final String cattr0type = "mobius.PCCCert";
    final byte[] cdata0 = new byte[]{0, 2, 1, 0, 0, 0, 0, 0, 0, 24, 84, 101, 115, 116, 32, 99, 101, 114, 116, 105, 102, 105, 99, 97, 116, 101, 32, 99, 111, 110, 116, 101, 110, 116};
    final Attribute cattr0 = new DefaultAttribute(cattr0type, cdata0);
    result.addAttribute(cattr0);
    final String cattr1type = "org.bmlspecs.SecondConstantPool";
    final byte[] cdata1 = new byte[]{0, 2, 0, 5, 0, 0, 0, 0, 0, 0, 0, 42};
    final Attribute cattr1 = new DefaultAttribute(cattr1type, cdata1);
    result.addAttribute(cattr1);
    final MethodName m0 = MethodName.get("<init>", "()V");
    final String m0attr0type = "Code";
    final byte[] m0data0 = new byte[]{0, 0, 0, 1, 0, 0, 0, 5, 42, -73, 0, 8, -79, 0, 0, 0, 0};
    final Attribute m0attr0 = new DefaultAttribute(m0attr0type, m0data0);
    result.addAttribute(m0, m0attr0);
    return result;
  }
  private MockClassFile makeTest7() {
    final MockClassFile result = new MockClassFile(ClassName.parseInternal("mobius.cct.testdata.Test7"));
    final String cattr0type = "mobius.PCCCert";
    final byte[] cdata0 = new byte[]{0, 1, 1, 0, 0, 0, 0, 0, 0, 24, 84, 101, 115, 116, 32, 99, 101, 114, 116, 105, 102, 105, 99, 97, 116, 101, 32, 99, 111, 110, 116, 101, 110, 116};
    final Attribute cattr0 = new DefaultAttribute(cattr0type, cdata0);
    result.addAttribute(cattr0);
    final String cattr1type = "org.bmlspecs.SecondConstantPool";
    final byte[] cdata1 = new byte[]{0, 2, 0, 5, 0, 0, 0, 0, 0, 0, 0, 42};
    final Attribute cattr1 = new DefaultAttribute(cattr1type, cdata1);
    result.addAttribute(cattr1);
    final MethodName m0 = MethodName.get("<init>", "()V");
    final String m0attr0type = "Code";
    final byte[] m0data0 = new byte[]{0, 0, 0, 1, 0, 0, 0, 5, 42, -73, 0, 8, -79, 0, 0, 0, 0};
    final Attribute m0attr0 = new DefaultAttribute(m0attr0type, m0data0);
    result.addAttribute(m0, m0attr0);
    return result;
  }
  private MockClassFile makeTest8() {
    final MockClassFile result = new MockClassFile(ClassName.parseInternal("mobius.cct.testdata.Test8"));
    final String cattr0type = "mobius.PCCCert";
    final byte[] cdata0 = new byte[]{0, 1, 1, 0, 0, 0, 0, 0, 0, 21, 84, 101, 115, 116, 32, 99, 101, 114, 116, 105, 102, 105, 99, 97, 116, 101, 32, 99, 111, 110, 116, 101, 110, 116};
    final Attribute cattr0 = new DefaultAttribute(cattr0type, cdata0);
    result.addAttribute(cattr0);
    final String cattr1type = "org.bmlspecs.SecondConstantPool";
    final byte[] cdata1 = new byte[]{0, 1, 0, 1, 0, 15, 109, 111, 98, 105, 117, 115, 46, 116, 101, 115, 116, 99, 101, 114, 116};
    final Attribute cattr1 = new DefaultAttribute(cattr1type, cdata1);
    result.addAttribute(cattr1);
    final MethodName m0 = MethodName.get("<init>", "()V");
    final String m0attr0type = "Code";
    final byte[] m0data0 = new byte[]{0, 0, 0, 1, 0, 0, 0, 5, 42, -73, 0, 8, -79, 0, 0, 0, 0};
    final Attribute m0attr0 = new DefaultAttribute(m0attr0type, m0data0);
    result.addAttribute(m0, m0attr0);
    return result;
  }
  private MockClassFile makeTest9() {
    final MockClassFile result = new MockClassFile(ClassName.parseInternal("mobius.cct.testdata.Test9"));
    final String cattr0type = "mobius.PCCCert";
    final byte[] cdata0 = new byte[]{0, 1, 1, 0, 0, 0, 0, 0, 0, 24, 84, 101, 115, 116, 32, 99, 101, 114, 116, 105, 102, 105, 99, 97, 116, 101, 32, 99, 111, 110, 116, 101, 110, 116};
    final Attribute cattr0 = new DefaultAttribute(cattr0type, cdata0);
    result.addAttribute(cattr0);
    final String cattr1type = "org.bmlspecs.SecondConstantPool";
    final byte[] cdata1 = new byte[]{0, 2, 1, 0, 15, 109, 111, 98, 105, 117, 115, 46, 116, 101, 115, 116, 99, 101, 114, 116};
    final Attribute cattr1 = new DefaultAttribute(cattr1type, cdata1);
    result.addAttribute(cattr1);
    final MethodName m0 = MethodName.get("<init>", "()V");
    final String m0attr0type = "Code";
    final byte[] m0data0 = new byte[]{0, 0, 0, 1, 0, 0, 0, 5, 42, -73, 0, 8, -79, 0, 0, 0, 0};
    final Attribute m0attr0 = new DefaultAttribute(m0attr0type, m0data0);
    result.addAttribute(m0, m0attr0);
    final String m0attr1type = "mobius.PCCMethodCert";
    final byte[] m0data1 = new byte[]{0, 1, 1, 0, 0, 0, 0, 24, 84, 101, 115, 116, 32, 99, 101, 114, 116, 105, 102, 105, 99, 97, 116, 101, 32, 99, 111, 110, 116, 101, 110, 116};
    final Attribute m0attr1 = new DefaultAttribute(m0attr1type, m0data1);
    result.addAttribute(m0, m0attr1);
    return result;
  }


  
}
