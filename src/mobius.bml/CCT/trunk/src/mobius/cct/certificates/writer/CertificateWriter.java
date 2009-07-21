package mobius.cct.certificates.writer;

import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.ClassCertificateVisitor;
import mobius.cct.certificates.DefaultCertificateParser;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.certificates.MethodCertificateVisitor;
import mobius.cct.classfile.Attribute;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.ClassVisitor;
import mobius.cct.classfile.MethodName;
import mobius.cct.classfile.MethodVisitor;
import mobius.cct.classfile.MutableClassFile;
import mobius.cct.constantpool.ConstantPool;
import mobius.cct.constantpool.ConstantPoolBuilder;
import mobius.cct.constantpool.DefaultBuilder;
import mobius.cct.constantpool.DefaultFactory;
import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.util.VisitorException;

/**
 * CertificateVisitor used to write certified classes.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CertificateWriter implements ClassCertificateVisitor {
  /**
   * Source class.
   */
  private final MutableClassFile fBase;
  
  /**
   * Class writer.
   */
  private final ClassVisitor fWriter;
  
  /**
   * Class-level certificates.
   */
  private final List<ClassCertificate> fClassCerts;
  
  /**
   * Map of method-level certificates.
   */
  private final Map<MethodName, List<MethodCertificate>> fMethodCerts;
  
  /**
   * Constant pool (null until created).
   */
  private ConstantPoolBuilder fSCP;
  
  /**
   * Constructor.
   * @param base The class file to which the certificates
   * will be added. Existing certificates will be removed.
   * @param os Output stream.
   */
  public CertificateWriter(final MutableClassFile base,
                           final OutputStream os) {
    fBase = base;
    fWriter = base.getWriter(os);
    fClassCerts = new ArrayList<ClassCertificate>();
    fMethodCerts = 
      new HashMap<MethodName, List<MethodCertificate>>();
  }

  /**
   * Does not have to be called.
   * @param cls Class name.
   */
  public void begin(final ClassName cls) {
  }

  /**
   * Write class with new certificates.
   * @throws VisitorException .
   */
  public void end() throws VisitorException {
    fBase.visit(new ClassFilter());
  }

  /**
   * Add class certificate.
   * @param cert Certficate.
   */
  public void visitClassCert(final ClassCertificate cert) {
    fClassCerts.add(cert);
  }

  /**
   * Get object used to add method certificates.
   * @param m Method name.
   * @return MethodCertificateVisitor which can be used to add
   * method certificates.
   */
  public MethodCertificateVisitor visitMethod(final MethodName m) {
    return new MethodWriter();
  }
  
  /**
   * Class used to add method certificates.
   * @author Tadeusz Sznuk (ts209501@gmail.com)
   */
  private class MethodWriter implements MethodCertificateVisitor {    
    /**
     * Certificate list for this method.
     */
    private List<MethodCertificate> fList;
    
    /**
     * begin().
     * @param m Method name.
     */
    public void begin(final MethodName m) {
      fList = fMethodCerts.get(m);
      if (fList == null) {
        fList = new LinkedList<MethodCertificate>();
        fMethodCerts.put(m, fList);
      }
    }

    /**
     * end().
     * Does not have to be called.
     */
    public void end() {
    }

    /**
     * Add method certificate.
     * @param cert Certificate.
     */
    public void visitMethodCert(final MethodCertificate cert) {
      fList.add(cert);
    }
    
  }
  
  /**
   * Visitor used to get information from source class
   * and write new class to output stream.
   * @author Tadeusz Sznuk (ts209501@gmail.com)
   */
  private class ClassFilter implements ClassVisitor {
    /**
     * begin().
     * @param cls Class name.
     * @throws VisitorException .
     */
    public void begin(final ClassName cls) 
      throws VisitorException {
      fWriter.begin(cls);
    }

    /**
     * end().
     * @throws VisitorException .
     */
    public void end() throws VisitorException {
      if (fSCP == null) {
        fSCP = new DefaultBuilder();
        updateScp();
        final ConstantPool scp = 
          fSCP.toConstantPool(new DefaultFactory());
        fWriter.visitAttribute(new SecondConstantPool(scp));        
      }
      final Iterator<ClassCertificate> i = fClassCerts.iterator();
      while (i.hasNext()) {
        final Attribute attr = 
          new ClassCertificateAttribute(i.next(), fSCP);
        fWriter.visitAttribute(attr);
      }
      fWriter.end();
    }

    /**
     * Visit attribute.
     * @param attr Attribute.
     * @throws VisitorException .
     */
    public void visitAttribute(final Attribute attr) 
      throws VisitorException {
      
      try {
        if (SecondConstantPool.ATTR.equals(attr.getName())) {
          final ConstantPool oldScp = 
            DefaultCertificateParser.parseSCP(attr);
          fSCP = new DefaultBuilder(oldScp);
          updateScp();
          final ConstantPool scp = 
            fSCP.toConstantPool(new DefaultFactory());
          fWriter.visitAttribute(new SecondConstantPool(scp));
        } else if (!ClassCertificate.ATTR.equals(attr.getName())) {
          fWriter.visitAttribute(attr);
        }
      } catch (VisitorException e) {
        throw e;
      } catch (InvalidFormatException e) {
        throw new VisitorException(e);
      }
    }

    /**
     * Visit method.
     * @param m Method name.
     * @return Method visitor.
     * @throws VisitorException .
     */
    public MethodVisitor visitMethod(final MethodName m) 
      throws VisitorException {
      return new MethodAttributeFilter();
    }
  }
  
  /**
   * Update second constant pool with constants needed by
   * new certificates. Old constants are not removed.
   */
  private void updateScp() {
    final Iterator<ClassCertificate> i = fClassCerts.iterator();
    while (i.hasNext()) {
      final ClassCertificate cert = i.next();
      fSCP.newUtf8(cert.getType());
      final Iterator<String> j = cert.getImports();
      while (j.hasNext()) {
        fSCP.newUtf8(j.next());
      }
    }
    final Iterator<List<MethodCertificate>> j = 
      fMethodCerts.values().iterator();
    while (j.hasNext()) {
      final Iterator<MethodCertificate> k = j.next().iterator();
      while (k.hasNext()) {
        fSCP.newUtf8(k.next().getType());
      }
    }
  }
  
  /**
   * Visitor used to get information from source class method
   * and write new method to output stream.
   * @author Tadeusz Sznuk (ts209501@gmail.com)
   */
  private class MethodAttributeFilter implements MethodVisitor {
    /**
     * Method writer.
     */
    private MethodVisitor fMethodWriter;
    
    /**
     * Method name.
     */
    private MethodName fMethod;
    
    /**
     * begin().
     * @param m Method name.
     * @throws VisitorException .
     */
    public void begin(final MethodName m) throws VisitorException {
      if (fSCP == null) {
        fSCP = new DefaultBuilder();
        updateScp();
        final ConstantPool scp = 
          fSCP.toConstantPool(new DefaultFactory());
        fWriter.visitAttribute(new SecondConstantPool(scp)); 
      }
      fMethodWriter = fWriter.visitMethod(m);
      fMethodWriter.begin(m);
      fMethod = m;
    }

    /**
     * Finished reading method - write certificates.
     * @throws VisitorException .
     */
    public void end() throws VisitorException {
      if (!fMethodCerts.containsKey(fMethod)) { return; }
      final Iterator<MethodCertificate> i = 
        fMethodCerts.get(fMethod).iterator();
      while (i.hasNext()) {
        final Attribute attr = 
          new MethodCertificateAttribute(i.next(), fSCP);
        fMethodWriter.visitAttribute(attr);
      }
      fMethodWriter.end();
    }

    /**
     * Visit attribute.
     * @param attr Attribute.
     * @throws VisitorException .
     */
    public void visitAttribute(final Attribute attr) 
      throws VisitorException {
      if (!MethodCertificate.ATTR.equals(attr.getName())) {
        fMethodWriter.visitAttribute(attr);
      }
    }
  }
}
