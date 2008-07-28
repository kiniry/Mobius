package mobius.cct.repositories.classfile;

import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.repositories.cp.ConstantPool;
import mobius.cct.repositories.cp.ConstantPoolBuilder;
import mobius.cct.repositories.cp.ConstantPoolFactory;
import mobius.cct.repositories.cp.DefaultBuilder;
import mobius.cct.repositories.cp.DefaultFactory;
import mobius.cct.repositories.cp.UnknownConstantException;
import mobius.cct.util.Function;
import mobius.cct.util.MappedIterator;
import mobius.cct.util.Version;

/**
 * Default implementation of class file. No external 
 * libraries (bcel, asm, ...) are used.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultClassFile implements MutableClassFile {
  /**
   * First four bytes of a class file.
   */
  private static final int MAGIC = 0xCAFEBABE;

  // ACCESS FLAGS
  /**
   * Declared public; may be accessed from outside its package.
   */
  private static final int ACC_PUBLIC = 0x0001;
  
  /**
   * Declared final; no subclasses allowed.
   */
  private static final int ACC_FINAL = 0x0010;
  
  /**
   *  Treat superclass methods specially when 
   *  invoked by the invokespecial instruction.
   */
  private static final int ACC_SUPER = 0x0020;
  
  /**
   * Is an interface, not a class.
   */
  private static final int ACC_INTERFACE = 0x0200; 
  
  /**
   * Declared abstract; must not be instantiated.
   */
  private static final int ACC_ABSTRACT = 0x0400; 
  
  /**
   * Declared synthetic; Not present in the source code.
   */
  private static final int ACC_SYNTHETIC = 0x1000; 
  
  /**
   * Declared as an annotation type.
   */
  private static final int ACC_ANNOTATION = 0x2000; 
  
  /**
   * Declared as an enum type.
   */
  private static final int ACC_ENUM = 0x4000; 

  /**
   * Version.
   */
  private final Version fVersion;
  
  /**
   * Constant pool.
   */
  private ConstantPool fConstantPool;
  
  /**
   * Access flags.
   */
  private final int fAccessFlags;
  
  /**
   * Index of class name in the constant pool.
   */
  private final int fClassName;
  
  /**
   * Index of superclass name in the constant pool.
   * 
   */
  private final int fSuperName;
  
  /**
   * Indices of names of implemented interfaces in the
   * constant pool.
   */
  private final int[] fInterfaces;
  
  /**
   * Fields.
   */
  private final Field[] fFields;
  
  /**
   * Methods.
   */
  private final Map<MethodName, Method> fMethods;
  
  /**
   * Attributes.
   */
  private final AttributeMap fAttributes;
  
  /**
   * Constructor - read class from input stream.
   * @param is Input stream.
   * @throws IOException if the file cannot be parsed. If its format is invalid,
   *    InvalidFormatException should be thrown.
   */
  public DefaultClassFile(final InputStream is) throws IOException {
    final DataInputStream ds = new DataInputStream(is);
    
    if (ds.readInt() != MAGIC) {
      throw new InvalidFormatException("Invalid header");
    }
    final int minor = ds.readUnsignedShort();
    final int major = ds.readUnsignedShort();
    fVersion = new Version(major, minor);

    fConstantPool = readConstantPool(ds);
    fAccessFlags = ds.readUnsignedShort();
    fClassName = ds.readUnsignedShort();
    fSuperName = ds.readUnsignedShort();
    
    fInterfaces = readInterfaces(ds);
    fFields = readFields(ds);
    fMethods = readMethods(ds);
    
    fAttributes = new AttributeMap(ds, fConstantPool);
  }

  /**
   * Read constant pool.
   * @param ds Input stream.
   * @return Constant pool.
   * @throws IOException .
   */
  private ConstantPool readConstantPool(final DataInputStream ds)
    throws IOException {
    
    final ConstantPoolFactory cpFactory = new DefaultFactory();
    try {
      return cpFactory.read(ds);
    } catch (UnknownConstantException e) {
      throw new InvalidFormatException("Invalid constant");
    }
  }
  
  /**
   * Read implemented interfaces.
   * @param ds Input stream.
   * @return Array of interfaces.
   * @throws IOException .
   */
  private int[] readInterfaces(final DataInputStream ds)
    throws IOException {
    
    final int interfacesCount = ds.readUnsignedShort();
    final int[] interfaces = new int[interfacesCount];
    for (int i = 0; i < interfacesCount; i++) {
      interfaces[i] = ds.readUnsignedShort();
    }
    return interfaces;
  }

  /**
   * Read fields info.
   * @param ds Input stream.
   * @return Array of fields.
   * @throws IOException .
   */
  private Field[] readFields(final DataInputStream ds)
    throws IOException {
    
    final int fieldCount = ds.readUnsignedShort();
    final Field[] fields = new Field[fieldCount];
    for (int i = 0; i < fieldCount; i++) {
      fields[i] = new Field(ds, fConstantPool);
    }
    return fields;
  }

  /**
   * Read methods info.
   * @param ds Input stream.
   * @return Map of methods.
   * @throws IOException .
   */
  private Map<MethodName, Method> 
  readMethods(final DataInputStream ds) throws IOException {
    final int methodCount = ds.readUnsignedShort();
    final Map<MethodName, Method> methods = 
      new HashMap<MethodName, Method>(methodCount);
    for (int i = 0; i < methodCount; i++) {
      final Method m = new Method(ds, fConstantPool);
      methods.put(m.getName(), m);
    }
    return methods;
  }

  /**
   * Return all methods of this class.
   * @return Iterator.
   */
  @Override
  public Iterator<MethodName> getMethods() {
    final Iterator<Method> methodIterator = fMethods.values().iterator();
    final Function<Method, MethodName> m = 
      new Function<Method, MethodName>() {
        public MethodName call(final Method m) {
          return m.getName();
        }
      };
    return 
      new MappedIterator<Method, MethodName>(methodIterator, m);
  }
  
  /**
   * Add class attribute.
   * @param attr Attribute.
   */
  @Override
  public void addClassAttr(final Attribute attr) {
    fAttributes.addAttribute(attr);    
  }

  /**
   * Add method attribute.
   * @param m Method name.
   * @param attr Attribute.
   */  
  @Override
  public void addMethodAttr(final MethodName m, 
                            final Attribute attr) {
    fMethods.get(m).getAttributes().addAttribute(attr);
  }

  /**
   * Get class attribute.
   * @param name Attribute name.
   * @param i Attribute index.
   * @return Attribute.
   */  
  @Override
  public Attribute getClassAttr(final String name, final int i) {
    return fAttributes.get(name, i);
  }

  /**
   * Get number of class attributes.
   * @param name Attribute name.
   * @return Attribute count.
   */  
  @Override
  public int getClassAttrCount(final String name) {
    return fAttributes.getCount(name);
  }
  
  /**
   * Get method attribute.
   * @param m Method name.
   * @param name Attribute name.
   * @param i Attribute index.
   * @return Attribute.
   */  
  @Override
  public Attribute getMethodAttr(final MethodName m, 
                                 final String name, 
                                 final int i) {
    return fMethods.get(m).getAttributes().get(name, i);
  }

  /**
   * Get number of method attributes.
   * @param m Method name.
   * @param name Attribute name.
   * @return Attribute count.
   */  
  @Override
  public int getMethodAttrCount(final MethodName m, 
                                final String name) {
    return fMethods.get(m).getAttributes().getCount(name);
  }

  /**
   * Remove class attribute.
   * @param name Attribute name.
   * @param i Attribute index.
   */  
  @Override
  public void removeClassAttr(final String name, final 
                              int i) {
    fAttributes.remove(name, i);
  }
  
  /**
   * Remove method attribute.
   * @param m Method name.
   * @param name Attribute name.
   * @param i Attribute index.
   */  
  @Override
  public void removeMethodAttr(final MethodName m, 
                               final String name, 
                               final int i) {
    fMethods.get(m).getAttributes().remove(name, i);
  }

  /**
   * Write class to output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  @Override
  public void writeTo(final OutputStream os) throws IOException {
    final ConstantPoolBuilder cp = updateConstantPool();
    final DataOutputStream ds = new DataOutputStream(os);
    
    ds.writeInt(MAGIC);
    ds.writeShort(fVersion.getMinor());
    ds.writeShort(fVersion.getMajor());
    fConstantPool.write(ds);
    ds.writeShort(fAccessFlags);
    ds.writeShort(fClassName);
    ds.writeShort(fSuperName);
    writeInterfaces(ds);
    writeFields(ds, cp);
    writeMethods(ds, cp);
    writeAttributes(ds, cp, fAttributes);
  }
  
  /**
   * Update constant pool - add entries for new attributes.
   * @return Updated constant pool as a builder.
   */
  private ConstantPoolBuilder updateConstantPool() {
    // DefaultBuilder will never change indices of existing consts...
    final ConstantPoolBuilder cp = new DefaultBuilder(fConstantPool);
    final Iterator<Attribute> i1 = classAttributes(); 
    while (i1.hasNext()) {
      cp.newUtf8(i1.next().getName());
    }
    final Iterator<Method> im = fMethods.values().iterator();
    while (im.hasNext()) {
      final Iterator<Attribute> i2 = 
        im.next().getAttributes().iterator();
      while (i2.hasNext()) {
        cp.newUtf8(i2.next().getName());
      }
    }
    return cp;
  }
  
  /**
   * Write implemented interfaces.
   * @param ds Output stream.
   * @throws IOException .
   */
  private void writeInterfaces(final DataOutputStream ds)
    throws IOException {
   
    ds.writeShort(fInterfaces.length);
    for (int i = 0; i < fInterfaces.length; i++) {
      ds.writeShort(fInterfaces[i]);
    }
  }

  /**
   * Write fields.
   * @param ds Output stream.
   * @param cp Constant pool.
   * @throws IOException .
   */
  private void writeFields(final DataOutputStream ds, 
                           final ConstantPoolBuilder cp)
    throws IOException {
   
    ds.writeShort(fFields.length);
    for (int i = 0; i < fFields.length; i++) {
      ds.writeShort(fFields[i].getAccessFlags());
      ds.writeShort(cp.newUtf8(fFields[i].getName()));
      ds.writeShort(cp.newUtf8(fFields[i].getType().internalForm()));
      writeAttributes(ds, cp, fFields[i].getAttributes());
    }
  }

  /**
   * Write methods.
   * @param ds Output stream.
   * @param cp Constant pool.
   * @throws IOException .
   */
  private void writeMethods(final DataOutputStream ds, 
                            final ConstantPoolBuilder cp)
    throws IOException {
   
    ds.writeShort(fMethods.size());
    final Iterator<Method> i = fMethods.values().iterator();
    while (i.hasNext()) {
      final Method m = i.next();
      ds.writeShort(m.getAccessFlags());
      ds.writeShort(cp.newUtf8(m.getName().getName()));
      ds.writeShort(cp.newUtf8(m.getName().getType().internalForm()));
      writeAttributes(ds, cp, m.getAttributes());
    }
  }
  
  /**
   * Write attribute set.
   * @param ds Output stream.
   * @param cp Constant pool.
   * @param a Attributes.
   * @throws IOException .
   */
  private void writeAttributes(final DataOutputStream ds, 
                               final ConstantPoolBuilder cp,
                               final AttributeMap a)
    throws IOException {
   
    final ByteArrayOutputStream os = new ByteArrayOutputStream();
    ds.writeShort(a.size());
    final Iterator<Attribute> i = a.iterator();
    while (i.hasNext()) {
      final Attribute attr = i.next();
      os.reset();
      attr.writeData(os);
      ds.writeShort(cp.newUtf8(attr.getName()));
      ds.writeShort(os.size());
      ds.write(os.toByteArray());
    }
  }
  
  /**
   * Get file version.
   * @return Version.
   */
  public Version getVersion() {
    return fVersion;
  }
  
  /**
   * Get all class attributes.
   * @return Iterator.
   */
  @Override
  public Iterator<Attribute> classAttributes() {
    return fAttributes.iterator();
  }
  /**
   * Get all attributes of a method.
   * @param m Method name.
   * @return Iterator.
   */
  @Override
  public Iterator<Attribute> methodAttributes(final MethodName m) {
    return fMethods.get(m).getAttributes().iterator();
  }
  /**
   * Return true if this class is public.
   * @return true iff ACC_PUBLIC flag is set.
   */
  public boolean isPublic() {
    return (fAccessFlags & ACC_PUBLIC) != 0;
  }
  /**
   * Return true if this class is final.
   * @return true iff ACC_FINAL flag is set.
   */
  public boolean isFinal() {
    return (fAccessFlags & ACC_FINAL) != 0;
  }
  /**
   * Return true if ACC_SUPER flag is set.
   * @return true iff ACC_SUPER flag is set.
   */
  public boolean isSuper() {
    return (fAccessFlags & ACC_SUPER) != 0;
  }
  /**
   * Return true if this object represents an interface.
   * @return true iff ACC_INTERFACE flag is set.
   */
  public boolean isInterface() {
    return (fAccessFlags & ACC_INTERFACE) != 0;
  }
  /**
   * Return true if this class is abstract.
   * @return true if ACC_ABSTRACT flag is set.
   */
  public boolean isAbstract() {
    return (fAccessFlags & ACC_ABSTRACT) != 0;
  }
  /**
   * Return true if this class is synthetic.
   * @return true if ACC_SYNTHETIC flag is set.
   */
  public boolean isSynthetic() {
    return (fAccessFlags & ACC_SYNTHETIC) != 0;
  }
  /**
   * Return true if this object represents an annotation.
   * @return true if ACC_ANNOTATION flag is set.
   */
  public boolean isAnnotation() {
    return (fAccessFlags & ACC_ANNOTATION) != 0;
  }
  /**
   * Return true if this object represents an enum.
   * @return true if ACC_ENUM flag is set.
   */
  public boolean isEnum() {
    return (fAccessFlags & ACC_ENUM) != 0;
  }  
}
