package mobius.cct.certificates.writer;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import mobius.cct.certificates.CertificatePack;
import mobius.cct.certificates.ClassCertificate;
import mobius.cct.certificates.MethodCertificate;
import mobius.cct.classfile.Attribute;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.DefaultClassFile;
import mobius.cct.classfile.Method;
import mobius.cct.classfile.MethodName;
import mobius.cct.repositories.cp.ConstantPoolBuilder;
import mobius.cct.repositories.cp.DefaultBuilder;
import mobius.cct.repositories.cp.DefaultFactory;

// TODO: REFACTOR!!!

/**
 * Class used to create certificate files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class CertificateFileWriter {
  /**
   * Major version.
   */
  private static final int MAJOR = 49;
  
  /**
   * Write certificate file to output stream.
   * @param cls Class name.
   * @param certs Array of certificates.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final ClassName cls,
                    final CertificatePack[] certs,
                    final OutputStream os) throws IOException {
    final ConstantPoolBuilder cp = new DefaultBuilder();
    final ConstantPoolBuilder scp = new DefaultBuilder();
    final DataOutputStream ds = new DataOutputStream(os);
    final int classFlags = 
      DefaultClassFile.ACC_ABSTRACT | DefaultClassFile.ACC_SUPER;
    final int methodFlags = Method.ACC_ABSTRACT;
    final Map<MethodName, List<MethodCertificate>> mm = 
      new HashMap<MethodName, List<MethodCertificate>>();
    
    cp.newClass(cls.internalForm());
    cp.newClass("java/lang/Object");
    cp.newUtf8(ClassCertificate.ATTR);
    cp.newUtf8(MethodCertificate.ATTR);
    cp.newUtf8(SecondConstantPool.ATTR);
    for (int i = 0; i < certs.length; i++) {
      final ClassCertificate cert = certs[i].getClassCertificate();
      scp.newUtf8(cert.getType());
      final Iterator<MethodName> j = certs[i].getCertifiedMethods();
      while (j.hasNext()) {
        final MethodName m = j.next();
        cp.newUtf8(m.getName());
        cp.newUtf8(m.getType().internalForm());
        final List<MethodCertificate> list;
        if (mm.containsKey(m)) {
          list = mm.get(m);
        } else {
          list = new LinkedList<MethodCertificate>();
          mm.put(m, list);
        }
        list.add(certs[i].getMethodCertificate(m));
      }
      final Iterator<String> k = cert.getImports();
      while (k.hasNext()) {
        scp.newUtf8(k.next());
      }
    }
    
    ds.writeInt(DefaultClassFile.MAGIC);
    ds.writeByte(0);
    ds.writeByte(MAJOR);
    cp.toConstantPool(new DefaultFactory()).write(ds);
    ds.writeShort(classFlags);
    ds.writeShort(cp.newClass(cls.internalForm()));
    ds.writeShort(cp.newClass("java/lang/Object"));
    
    ds.writeShort(0);
    
    ds.writeShort(mm.size());
    final Iterator<Entry<MethodName, List<MethodCertificate>>> i =
      mm.entrySet().iterator();
    while (i.hasNext()) {
      final Entry<MethodName, List<MethodCertificate>> e = i.next();
      final MethodName m = e.getKey();
      final Iterator<MethodCertificate> j = e.getValue().iterator();
      ds.writeShort(methodFlags);
      ds.writeShort(cp.newUtf8(m.getName()));
      ds.writeShort(cp.newUtf8(m.getType().internalForm()));
      ds.writeShort(e.getValue().size());
      while (j.hasNext()) {
        final Attribute a = 
          new MethodCertificateAttribute(j.next(), scp);
        writeAttribute(a, cp, ds);
      }
    }
    ds.writeShort(certs.length + 1);
    writeAttribute(new SecondConstantPool(
        scp.toConstantPool(new DefaultFactory())), cp, ds
    );
    for (int j = 0; j < certs.length; j++) {
      final Attribute a = 
        new ClassCertificateAttribute(
          certs[j].getClassCertificate(), scp
        );
      writeAttribute(a, cp, ds);
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

    ds.writeShort(cp.newUtf8(MethodCertificate.ATTR));
    ds.writeInt(bos.size());
    a.writeData(ds);    
  }
}
