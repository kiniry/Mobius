package mobius.cct.certificates;

import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.MethodName;
import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.util.EmptyIterator;
import mobius.cct.util.FlattenIterator;
import mobius.cct.util.Function;
import mobius.cct.util.GetMapValues;
import mobius.cct.util.MappedIterator;
import mobius.cct.util.Version;
import mobius.cct.util.VisitorException;

/**
 * A CertificateCollector collects all certificates
 * from a class. Can be used multiple times. Certificates
 * with the same type and version are merged.
 * @param <C> Type of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CertificateCollector<C extends ClassFile> {
  /**
   * Collected CertificatePacks.
   */
  private final Map<String, Map<Version, CertificatePack>> fCerts;
  
  /**
   * Constructor.
   */
  public CertificateCollector() {
    fCerts = new HashMap<String, Map<Version, CertificatePack>>();
  }
 
  /**
   * Collect certificates from a class.
   * @param parser Parser used to read certificates.
   * @param cls Class file.
   * @throws IOException .
   */
  public void collect(
                      final CertificateParser<? super C> parser,
                      final C cls) throws IOException {
    try {
      parser.parse(cls, new ClassCertVisitor());
    } catch (IOException e) {
      throw e;
    } catch (VisitorException e) {
      if (e.getCause() instanceof IOException) {
        throw (IOException)e.getCause();
      } else {
        throw new InvalidFormatException(e.getMessage());
      }
    }
  }
  
  /**
   * Add certificate pack.
   * @param c Certificate pack.
   */
  public void addCertificates(final CertificatePack c) {
    final String type = c.getType();
    final Version version = c.getVersion();
    final Map<Version, CertificatePack> m;
    if (fCerts.containsKey(type)) {
      m = fCerts.get(type);
    } else {
      m = new TreeMap<Version, CertificatePack>();
      fCerts.put(type, m);
    }
    if (m.containsKey(version)) {
      m.put(version, m.get(version).merge(c));
    } else {
      m.put(version, c);
    }
  }
  
  /**
   * Add method certificate. Class certificate
   * with the same signature must already exist.
   * If a method certificate with identical signature
   * exists, it is replaced.
   * @param m Method certificate.
   */
  public void addMethodCert(final MethodCertificate m) {
    final Map<Version, CertificatePack> map = 
      fCerts.get(m.getType());
    if (map != null) {
      final CertificatePack p = map.get(m.getVersion());
      if (p != null) {
        map.put(m.getVersion(), p.setMethodCert(m));
      }
    }
  }
  
  /**
   * Get certificate pack. Returns null if there are no
   * certificates with requested type and version.
   * @param type Certificate type.
   * @param version Certificate version.
   * @return CertificatePacl or null.
   */
  public CertificatePack getCertificatePack(final String type,
                                            final Version version) {
    final Map<Version, CertificatePack> m = fCerts.get(type);
    if (m == null) {
      return null;
    } else {
      return m.get(version);
    }
  }
  
  /**
   * Get all certificates of given type.
   * @param type Certificate type.
   * @return Iterator.
   */
  public Iterator<CertificatePack> getCertificates(final String type) {
    final Map<Version, CertificatePack> m = fCerts.get(type);
    if (m == null) {
      return new EmptyIterator<CertificatePack>();
    } else {
      return m.values().iterator();
    }    
  }
  
  /**
   * Get all certificates.
   * @return Iterator.
   */
  public Iterator<CertificatePack> getAllCertificates() {
    final Iterator<Map<Version, CertificatePack>> i1 = 
      fCerts.values().iterator();
    final Function<Map<Version, CertificatePack>, 
             Iterator<CertificatePack>> f = 
      new GetMapValues<Version, CertificatePack>();
    final Iterator<Iterator<CertificatePack>> i2 = 
      new MappedIterator<Map<Version, CertificatePack>, 
                         Iterator<CertificatePack>>(i1, f);
    return new FlattenIterator<CertificatePack>(i2);
  }
  
  /**
   * Remove all certificates of given type and version.
   * @param t Certificate type.
   * @param v Certificate version.
   */
  public void removeCerts(final String t, final Version v) {
    final Map<Version, CertificatePack> m;
    if (fCerts.containsKey(t)) {
      m = fCerts.get(t);
      m.remove(v);
    }
  }
  
  /**
   * Collect method certificates in a multimap.
   * @return Mutlimap with method certificates.
   */
  private Map<MethodName, List<MethodCertificate>> methodMap() {
    final Map<MethodName, List<MethodCertificate>> m;
    m = new HashMap<MethodName, List<MethodCertificate>>();
    final Iterator<CertificatePack> i = getAllCertificates();
    while (i.hasNext()) {
      final CertificatePack p = i.next();
      final Iterator<MethodCertificate> j = p.getMethodCerts();
      while (j.hasNext()) {
        final MethodCertificate mc = j.next();
        final List<MethodCertificate> l;
        if (m.containsKey(mc.getMethod())) {
          l = m.get(mc.getMethod());
        } else {
          l = new LinkedList<MethodCertificate>();
          m.put(mc.getMethod(), l);
        }
        l.add(mc);
      }
    }
    return m;
  }
  
  /**
   * Visit collected certificates.
   * @param v Certificate visitor.
   * @param c Class name.
   * @throws VisitorException .
   */
  public void visitCertificates(final ClassCertificateVisitor v, 
                                final ClassName c) 
    throws VisitorException {
    
    final Map<MethodName, List<MethodCertificate>> m;
    m = methodMap();
    
    v.begin(c);
    final Iterator<CertificatePack> i = getAllCertificates();
    while (i.hasNext()) {
      final CertificatePack p = i.next();
      v.visitClassCert(p.getClassCertificate());
    }
    final Iterator<MethodName> j = m.keySet().iterator();
    while (j.hasNext()) {
      final MethodName mn = j.next();
      final MethodCertificateVisitor mv = v.visitMethod(mn);
      if (mv != null) {
        mv.begin(mn);
        final Iterator<MethodCertificate> k = m.get(mn).iterator();
        while (k.hasNext()) {
          mv.visitMethodCert(k.next());
        }
        mv.end();
      }
    }
    v.end();
  }
  
  /**
   * Visitor used to read certificates.
   * @author Tadeusz Sznuk (ts209501@gmail.com)
   */
  private class ClassCertVisitor implements ClassCertificateVisitor {
    /**
     * Map of certificate builders.
     */
    private Map<CertificateSignature, CertificatePackBuilder> fBuilders;
    
    /**
     * begin().
     * @param cls Class name.
     */
    public void begin(final ClassName cls) {
      fBuilders = 
        new HashMap<CertificateSignature, CertificatePackBuilder>();
    }

    /**
     * end().
     */
    public void end() {
      final Iterator<CertificatePackBuilder> i = 
        fBuilders.values().iterator();
      while (i.hasNext()) {
        final CertificatePackBuilder c = i.next();
        addCertificates(c.toCertificatePack());
      }
    }

    /**
     * Visit class certificate.
     * @param cert Certificate.
     */
    public void visitClassCert(final ClassCertificate cert) {
      final CertificateSignature sig = cert.getSignature();
      if (fBuilders.containsKey(sig)) {
        fBuilders.get(sig).mergeClassCert(cert);
      } else {
        fBuilders.put(sig, new CertificatePackBuilder(cert));
      }
    }

    /**
     * Visit method.
     * @param m Method name.
     * @return Visitor used to collect method certificates.
     */
    public MethodCertificateVisitor visitMethod(final MethodName m) {
      return new MethodCertVisitor();
    }
    
    /**
     * Visitor used to collect method certificates.
     * @author Tadeusz Sznuk (ts209501@gmail.com)
     */
    private class MethodCertVisitor 
      implements MethodCertificateVisitor {
      /**
       * begin().
       * @param m Method name.
       */
      public void begin(final MethodName m) {
      }

      /**
       * end().
       */
      public void end() {
      }

      /**
       * Visit method certificate.
       * @param cert Method certificate.
       */
      public void visitMethodCert(final MethodCertificate cert) {
        final CertificateSignature sig = cert.getSignature();
        if (!fBuilders.containsKey(sig)) {
          final ClassCertificate c = new ClassCertificate(
            sig.getType(), sig.getVersion(), 
            new String[]{}, new byte[]{}
          );
          fBuilders.put(sig, new CertificatePackBuilder(c));
        }
        fBuilders.get(sig).addMethodCert(cert);
      }
    }
  }
}
