package mobius.cct.tests.mocks;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import mobius.cct.certificates.CertificatePack;
import mobius.cct.certificates.CertificateParser;
import mobius.cct.certificates.ClassCertificateVisitor;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.certificates.MethodCertificateVisitor;
import mobius.cct.classfile.MethodName;
import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.util.VisitorException;

/**
 * Mock implementation of CertificateParser
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockCertificateParser implements
  CertificateParser<MockRepoClass> {

  public void parse(MockRepoClass c, ClassCertificateVisitor v)
      throws InvalidFormatException, VisitorException {
    final CertificatePack[] certs = c.getCerts();
    final Map<MethodName, List<MethodCertificate>> mm = 
      new HashMap<MethodName, List<MethodCertificate>>();
    v.begin(c.getName());
    for (int i = 0; i < certs.length; i++) {
      v.visitClassCert(certs[i].getClassCertificate());
      Iterator<MethodName> j = certs[i].getCertifiedMethods();
      while (j.hasNext()) {
        final MethodName m = j.next();
        if (!mm.containsKey(m)) {
          mm.put(m, new LinkedList<MethodCertificate>());
        } 
        mm.get(m).add(certs[i].getMethodCertificate(m));
      }
    }
    final Iterator<MethodName> j = mm.keySet().iterator();
    while (j.hasNext()) {
      final MethodName m = j.next();
      final MethodCertificateVisitor mv = v.visitMethod(m);
      if (mv == null) {
        continue;
      }
      mv.begin(m);
      final Iterator<MethodCertificate> k = mm.get(m).iterator();
      while (k.hasNext()) {
        mv.visitMethodCert(k.next());
      }
      mv.end();
    }
    v.end();
  }


}
