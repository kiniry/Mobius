package mobius.cct.classfile;

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

import mobius.cct.constantpool.ConstantPoolBuilder;
import mobius.cct.constantpool.DefaultBuilder;
import mobius.cct.constantpool.DefaultFactory;
import mobius.cct.util.VisitorException;

/**
 * Default implementation of class writer.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultWriter implements ClassVisitor {
  /**
   * Source class.
   */
  private final DefaultClassFile fSource;
  
  /**
   * Output stream.
   */
  private final DataOutputStream fOutput;
  
  /**
   * New attributes.
   */
  private final List<Attribute> fAttributes;
  
  /**
   * New method attributes.
   */
  private final Map<MethodName, List<Attribute>> fMethodAttrs;
  
  /**
   * Constant pool.
   */
  private final ConstantPoolBuilder fConstantPool;
  
  /**
   * Constructor.
   * @param src Source class.
   * @param os Output stream.
   */
  public DefaultWriter(final DefaultClassFile src, 
                       final OutputStream os) {
    fSource = src;
    fOutput = new DataOutputStream(os);
    fAttributes = new ArrayList<Attribute>();
    fMethodAttrs = new HashMap<MethodName, List<Attribute>>();
    fConstantPool = new DefaultBuilder(src.getConstantPool());
    
    final Iterator<Method> i = fSource.getMethods();
    while (i.hasNext()) {
      final Method m = i.next();
      fMethodAttrs.put(m.getName(), new LinkedList<Attribute>());
    }
  }

  /**
   * Start class writing. 
   * @param cls Class name.
   * @throws VisitorException .
   */
  public void begin(final ClassName cls) throws VisitorException {
  }

  /**
   * Write collected information to the output stream.
   * @throws VisitorException .
   */
  public void end() throws VisitorException {
    try {
      write();
    } catch (IOException e) {
      throw new VisitorException(e);
    }
  }

  /**
   * Visit attribute.
   * @param attr Attribute.
   */
  public void visitAttribute(final Attribute attr) {
    fAttributes.add(attr);
    fConstantPool.newUtf8(attr.getName());
  }

  /**
   * Visit method.
   * @param m Method name.
   * @return Method visitor.
   */
  public MethodVisitor visitMethod(final MethodName m) {
    return new MethodWriter();
  }
  
  /**
   * Class used to collect method attributes.
   * @author Tadeusz Sznuk (ts209501@gmail.com)
   */
  private class MethodWriter implements MethodVisitor {
    /**
     * Collected method attributes.
     */
    private List<Attribute> fAttrs;

    /**
     * begin().
     * @param m Method name.
     * @throws VisitorException .
     */
    public void begin(final MethodName m) throws VisitorException {
      fAttrs = fMethodAttrs.get(m);
      if (fAttrs == null) {
        throw new VisitorException("Method not in class.");
      }
    }

    /**
     * end().
     */
    public void end() {
    }

    /**
     * Visit method attribute.
     * @param attr Attribute.
     */
    public void visitAttribute(final Attribute attr) {
      fAttrs.add(attr);
      fConstantPool.newUtf8(attr.getName());
    }
    
  }
  
  /**
   * Write class to output stream.
   * @throws IOException .
   */
  private void write() throws IOException {
    fOutput.writeInt(DefaultClassFile.MAGIC);
    fOutput.writeShort(fSource.getVersion().getMinor());
    fOutput.writeShort(fSource.getVersion().getMajor());
    fConstantPool.toConstantPool(
      new DefaultFactory()).write(fOutput);
    fOutput.writeShort(fSource.getAccessFlags());
    fOutput.writeShort(
      fConstantPool.newClass(fSource.getName().internalForm())
    );
    fOutput.writeShort(
      fConstantPool.newClass(fSource.getSuperName().internalForm())
    );
    writeInterfaces();
    writeFields();
    writeMethods();
    writeAttributes(fAttributes.iterator(), fAttributes.size());
  }
  
  /**
   * Write implemented interfaces.
   * @throws IOException .
   */
  private void writeInterfaces()
    throws IOException {
   
    fOutput.writeShort(fSource.interfaceCount());
    final Iterator<ClassName> i = fSource.getInterfaces();
    while (i.hasNext()) {
      fOutput.writeShort(
        fConstantPool.newClass(i.next().internalForm())
      );
    }
  }

  /**
   * Write fields.
   * @throws IOException .
   */
  private void writeFields()
    throws IOException {
   
    fOutput.writeShort(fSource.fieldCount());
    final Iterator<Field> i = fSource.getFields();
    while (i.hasNext()) {
      final Field f = i.next();
      fOutput.writeShort(f.getAccessFlags());
      fOutput.writeShort(fConstantPool.newUtf8(f.getName()));
      fOutput.writeShort(
        fConstantPool.newUtf8(f.getType().internalForm())
      );
      writeAttributes(f.getAttributes().iterator(), 
                      f.getAttributes().size());
    }
  }

  /**
   * Write methods.
   * @throws IOException .
   */
  private void writeMethods()
    throws IOException {
   
    fOutput.writeShort(fMethodAttrs.size());
    final Iterator<Method> i = fSource.getMethods();
    while (i.hasNext()) {
      final Method m = i.next();
      final MethodName mn = m.getName();
      fOutput.writeShort(m.getAccessFlags());
      fOutput.writeShort(
        fConstantPool.newUtf8(mn.getName())
      );
      fOutput.writeShort(
        fConstantPool.newUtf8(mn.getType().internalForm())
      );
      writeAttributes(fMethodAttrs.get(mn).iterator(), 
                      fMethodAttrs.get(mn).size());
    }
  }
  
  /**
   * Write attribute map.
   * @param i Attributes.
   * @param count Number of attributes.
   * @throws IOException .
   */
  private void writeAttributes(final Iterator<Attribute> i, 
                               final int count)
    throws IOException {
   
    final ByteArrayOutputStream os = new ByteArrayOutputStream();
    fOutput.writeShort(count);
    while (i.hasNext()) {
      final Attribute attr = i.next();
      os.reset();
      attr.writeData(os);
      fOutput.writeShort(fConstantPool.newUtf8(attr.getName()));
      fOutput.writeInt(os.size());
      fOutput.write(os.toByteArray());
    }
  }
  
}
