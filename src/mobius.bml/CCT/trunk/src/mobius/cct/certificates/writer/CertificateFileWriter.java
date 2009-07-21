package mobius.cct.certificates.writer;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.ClassCertificateVisitor;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.certificates.MethodCertificateVisitor;
import mobius.cct.classfile.Attribute;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.DefaultClassFile;
import mobius.cct.classfile.Method;
import mobius.cct.classfile.MethodName;
import mobius.cct.constantpool.ConstantPoolBuilder;
import mobius.cct.constantpool.DefaultBuilder;
import mobius.cct.constantpool.DefaultFactory;
import mobius.cct.util.Pair;
import mobius.cct.util.VisitorException;


/**
 * Class used to create certificate files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class CertificateFileWriter 
  implements ClassCertificateVisitor {
  /**
   * Major version.
   */
  private static final int MAJOR = 49;
  
  /**
   * Class name.
   */
  private final ClassName fClass;
  
  /**
   * Output stream.
   */
  private final DataOutputStream fOutput;
  
  /**
   * Class-level certificates.
   */
  private final List<ClassCertificate> fClassCerts;
  
  /**
   * Map of method-level certificates.
   */
  private final Map<MethodName, List<MethodCertificate>> fMethodCerts;
  
  /**
   * Constructor.
   * @param cls Class name.
   * @param os Output stream.
   */
  public CertificateFileWriter(final ClassName cls,
                               final OutputStream os) {
    fClass = cls;
    fOutput = new DataOutputStream(os);
    fClassCerts = new ArrayList<ClassCertificate>();
    fMethodCerts = 
      new HashMap<MethodName, List<MethodCertificate>>();
  }
  
  /**
   * Construct constant pools.
   * @return First and second contant pools.
   */
  private Pair<ConstantPoolBuilder, ConstantPoolBuilder> 
  createConstantPools() {
    final ConstantPoolBuilder cp = new DefaultBuilder();
    final ConstantPoolBuilder scp = new DefaultBuilder();
    
    cp.newClass(fClass.internalForm());
    cp.newClass("java/lang/Object");
    cp.newUtf8(ClassCertificate.ATTR);
    cp.newUtf8(MethodCertificate.ATTR);
    cp.newUtf8(SecondConstantPool.ATTR);
    final Iterator<ClassCertificate> i = fClassCerts.iterator();
    while (i.hasNext()) {
      final ClassCertificate cert = i.next();
      scp.newUtf8(cert.getType());
      final Iterator<String> k = cert.getImports();
      while (k.hasNext()) {
        scp.newUtf8(k.next());
      }
    }
    final Iterator<MethodName> j = fMethodCerts.keySet().iterator();
    while (j.hasNext()) {
      final MethodName m = j.next();
      cp.newUtf8(m.getName());
      cp.newUtf8(m.getType().internalForm());
      final Iterator<MethodCertificate> k = 
        fMethodCerts.get(m).iterator();
      while (k.hasNext()) {
        scp.newUtf8(k.next().getType());
      }
    }
    return new Pair<ConstantPoolBuilder, 
                    ConstantPoolBuilder>(cp, scp);
  }
  
  /**
   * Write methods.
   * @param cp Constant pool.
   * @param scp Second contant pool.
   * @throws IOException .
   */
  private void writeMethods(final ConstantPoolBuilder cp,
                            final ConstantPoolBuilder scp)
    throws IOException {
    
    final int methodFlags = Method.ACC_ABSTRACT;
    fOutput.writeShort(fMethodCerts.size());
    final Iterator<Entry<MethodName, List<MethodCertificate>>> i =
      fMethodCerts.entrySet().iterator();
    while (i.hasNext()) {
      final Entry<MethodName, List<MethodCertificate>> e = i.next();
      final MethodName m = e.getKey();
      final Iterator<MethodCertificate> j = e.getValue().iterator();
      fOutput.writeShort(methodFlags);
      fOutput.writeShort(cp.newUtf8(m.getName()));
      fOutput.writeShort(cp.newUtf8(m.getType().internalForm()));
      fOutput.writeShort(e.getValue().size());
      while (j.hasNext()) {
        final Attribute a = 
          new MethodCertificateAttribute(j.next(), scp);
        writeAttribute(a, cp, fOutput);
      }
    }
  }
  
  /**
   * Write class certificates.
   * @param cp Constant pool.
   * @param scp Second contant pool.
   * @throws IOException .
   */
  private void writeCerts(final ConstantPoolBuilder cp,
                          final ConstantPoolBuilder scp)
    throws IOException {

    final Iterator<ClassCertificate> i = fClassCerts.iterator();
    while (i.hasNext()) {
      final Attribute a = 
        new ClassCertificateAttribute(i.next(), scp);
      writeAttribute(a, cp, fOutput);
    }
  }
  
  /**
   * Write attribute.
   * @param a Attribute.
   * @param cp Constant pool.
   * @param ds Output stream.
   * @throws IOException .
   */
  private void writeAttribute(final Attribute a,
                              final ConstantPoolBuilder cp,
                              final DataOutputStream ds) 
    throws IOException {
    
    final ByteArrayOutputStream bos = 
      new ByteArrayOutputStream();
    a.writeData(bos);

    ds.writeShort(cp.newUtf8(a.getName()));
    ds.writeInt(bos.size());
    a.writeData(ds);    
  }

  /**
   * begin(). 
   * Does not have to be called.
   * @param cls Class name.
   */
  public void begin(final ClassName cls) {    
  }

  /**
   * Write certificate file to output stream.
   * @throws VisitorException .
   */
  public void end() throws VisitorException {
    final int classFlags = 
      DefaultClassFile.ACC_ABSTRACT | DefaultClassFile.ACC_SUPER;
    final Pair<ConstantPoolBuilder, ConstantPoolBuilder> pools = 
      createConstantPools();
    final ConstantPoolBuilder cp = pools.getFirst();
    final ConstantPoolBuilder scp = pools.getSecond();
    
    try {
      fOutput.writeInt(DefaultClassFile.MAGIC);
      fOutput.writeShort(0);
      fOutput.writeShort(MAJOR);
      cp.toConstantPool(new DefaultFactory()).write(fOutput);
      fOutput.writeShort(classFlags);
      fOutput.writeShort(cp.newClass(fClass.internalForm()));
      fOutput.writeShort(cp.newClass("java/lang/Object"));
      
      // Interfaces.
      fOutput.writeShort(0);
      
      // Fields.
      fOutput.writeShort(0);
      
      writeMethods(cp, scp);
      
      fOutput.writeShort(fClassCerts.size() + 1);
      writeAttribute(new SecondConstantPool(
          scp.toConstantPool(new DefaultFactory())), cp, fOutput
      );
      writeCerts(cp, scp);
    } catch (IOException e) {
      throw new VisitorException(e);
    }
  }

  /**
   * Add class certificate.
   * @param cert Certificate.
   */
  public void visitClassCert(final ClassCertificate cert) {
    fClassCerts.add(cert);
  }

  /**
   * Visit method.
   * @param m Method name.
   * @return Visitor which can be used to add method certificates.
   */
  public MethodCertificateVisitor visitMethod(final MethodName m) {
    return new MethodWriter();
  }
  
  /**
   * Class used to collect method certificates.
   * @author Tadeusz Sznuk (ts209501@gmail.com)
   */
  private final class MethodWriter 
    implements MethodCertificateVisitor {
    /**
     * List of method certificates.
     */
    private List<MethodCertificate> fList;
    
    /**
     * Begin visiting method.
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
     */
    public void end() {
    }

    /**
     * Add method certificate.
     * @param cert Method certificate.
     */
    public void visitMethodCert(final MethodCertificate cert) {
      fList.add(cert);
    }
  }
}
