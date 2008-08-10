package mobius.cct.tests.certificates;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.util.Iterator;

import mobius.cct.certificates.CertificateCollector;
import mobius.cct.certificates.CertificatePack;
import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.DefaultCertificateParser;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.certificates.MethodCertificateVisitor;
import mobius.cct.certificates.writer.CertificateFileWriter;
import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.DefaultClassFile;
import mobius.cct.classfile.DefaultClassReader;
import mobius.cct.classfile.MethodName;
import mobius.cct.util.Version;

import org.junit.Test;

/**
 * Tests of certificate file writer.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CertificateFileWriterTest {
  
  /**
   * Write simple certificate and read it back.
   */
  @Test
  public void testRW() throws Exception {
    final ClassCertificate cert = new ClassCertificate(
      "mobius.cct.testcert", new Version(42, 0), 
      new String[]{}, "Test certificate".getBytes()
    );
    final MethodName m = MethodName.get("<init>", "()V");
    final MethodCertificate mcert = new MethodCertificate(
      m, "mobius.cct.testcert", new Version(42, 0),
      "Method certificate".getBytes()
    );
    final ByteArrayOutputStream bos = 
      new ByteArrayOutputStream();
    final ClassName cls = ClassName.parseInternal("Test");
    final CertificateFileWriter w = 
      new CertificateFileWriter(cls, bos);
    w.begin(cls);
    w.visitClassCert(cert);
    final MethodCertificateVisitor mv = w.visitMethod(m);
    assertNotNull(mv);
    mv.begin(m);
    mv.visitMethodCert(mcert);
    mv.end();
    w.end();
    final ByteArrayInputStream bis = 
      new ByteArrayInputStream(bos.toByteArray());
    final DefaultClassReader reader = new DefaultClassReader();
    final DefaultClassFile f = reader.read(bis);
    final DefaultCertificateParser<ClassFile> parser = 
      new DefaultCertificateParser<ClassFile>();
    final CertificateCollector<ClassFile> collector = 
      new CertificateCollector<ClassFile>();
    collector.collect(parser, f);
    final Iterator<CertificatePack> i = 
      collector.getAllCertificates();
    assertTrue(i.hasNext());
    final CertificatePack p = i.next();
    assertFalse(i.hasNext());
    ClassCertificateTest.assertClassCertsEq(
      cert, p.getClassCertificate()
    );
    final Iterator<MethodName> j = p.getCertifiedMethods();
    assertTrue(j.hasNext());
    final MethodName m2 = j.next();
    assertEquals(m, m2);
    assertFalse(j.hasNext());
    MethodCertificateTest.assertMethodCertsEq(
      mcert, p.getMethodCertificate(m2)
    );
  }
}
