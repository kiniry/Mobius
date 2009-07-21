package mobius.cct.classfile;

import java.io.DataInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import mobius.cct.constantpool.ConstantPool;
import mobius.cct.constantpool.ConstantPoolFactory;
import mobius.cct.constantpool.DefaultFactory;
import mobius.cct.constantpool.DefaultPool;
import mobius.cct.constantpool.IllegalIndexException;
import mobius.cct.constantpool.UnknownConstantException;
import mobius.cct.constantpool.entries.ClassEntry;
import mobius.cct.constantpool.entries.Entry;
import mobius.cct.repositories.InvalidFormatException;
import mobius.cct.util.ArrayIterator;
import mobius.cct.util.Version;
import mobius.cct.util.VisitorException;

/**
 * Default implementation of class file. No external 
 * libraries (bcel, asm, ...) are used.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultClassFile implements MutableClassFile {
  /**
   * First four bytes of a class file.
   */
  public static final int MAGIC = 0xCAFEBABE;

  // ACCESS FLAGS
  /**
   * Declared public; may be accessed from outside its package.
   */
  public static final int ACC_PUBLIC = 0x0001;
  
  /**
   * Declared final; no subclasses allowed.
   */
  public static final int ACC_FINAL = 0x0010;
  
  /**
   *  Treat superclass methods specially when 
   *  invoked by the invokespecial instruction.
   */
  public static final int ACC_SUPER = 0x0020;
  
  /**
   * Is an interface, not a class.
   */
  public static final int ACC_INTERFACE = 0x0200; 
  
  /**
   * Declared abstract; must not be instantiated.
   */
  public static final int ACC_ABSTRACT = 0x0400; 
  
  /**
   * Declared synthetic; Not present in the source code.
   */
  public static final int ACC_SYNTHETIC = 0x1000; 
  
  /**
   * Declared as an annotation type.
   */
  public static final int ACC_ANNOTATION = 0x2000; 
  
  /**
   * Declared as an enum type.
   */
  public static final int ACC_ENUM = 0x4000; 

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
   * Zero for java/lang/Object.
   */
  private final int fSuper;
  
  /**
   * Names of implemented interfaces.
   */
  private final ClassName[] fInterfaces;
  
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
   * Parsed class name.
   */
  private ClassName fName;

  /**
   * Parsed superclass name.
   * Null for java/lang/Object.
   */
  private ClassName fSuperName;
  
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
    fVersion = readVersion(ds);

    fConstantPool = readConstantPool(ds);
    fAccessFlags = ds.readUnsignedShort();
    fClassName = ds.readUnsignedShort();
    fSuper = ds.readUnsignedShort();
    
    if (fSuper == 0) {
      fSuperName = null;
    } else {
      fSuperName = parseName(fSuper);
    }
    fName = parseName(fClassName);
    fInterfaces = readInterfaces(ds);
    fFields = readFields(ds);
    fMethods = readMethods(ds);
    
    fAttributes = new AttributeMap(ds, fConstantPool);
  }
  
  /**
   * Read version.
   * @param ds Input stream.
   * @return Parsed version.
   * @throws IOException .
   */
  private Version readVersion(final DataInputStream ds) 
    throws IOException {
    final int minor = ds.readUnsignedShort();
    final int major = ds.readUnsignedShort();
    return new Version(major, minor);
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
  private ClassName[] readInterfaces(final DataInputStream ds)
    throws IOException {
    
    final int interfacesCount = ds.readUnsignedShort();
    final ClassName[] interfaces = new ClassName[interfacesCount];
    for (int i = 0; i < interfacesCount; i++) {
      interfaces[i] = parseName(ds.readUnsignedShort());
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
   * Parse class name.
   * @param n Class name as index in the constant pool.
   * @return Class name.
   * @throws InvalidFormatException .
   */
  private ClassName parseName(final int n) 
    throws InvalidFormatException {
    final Entry classEntry;
    
    try {
      classEntry = fConstantPool.getEntry(n);
    } catch (IllegalIndexException e) {
      throw new InvalidFormatException("Invalid class name.");
    }
    if (!(classEntry instanceof ClassEntry)) {
      throw new InvalidFormatException("Invalid class name.");
    }
    final int nameIndex = ((ClassEntry)classEntry).getName();
    final String name = 
      DefaultPool.getString(fConstantPool, nameIndex);
    if (name == null) {
      throw new InvalidFormatException("Invalid class name.");
    }
    return ClassName.parseInternal(name);
  }
  
  /**
   * Visit class.
   * @param v Visitor.
   * @throws VisitorException .
   */
  public void visit(final ClassVisitor v) throws VisitorException {
    v.begin(fName);
    final Iterator<Attribute> ia = fAttributes.iterator();
    while (ia.hasNext()) {
      v.visitAttribute(ia.next());
    }
    final Iterator<Method> im = fMethods.values().iterator();
    while (im.hasNext()) {
      final Method m = im.next();
      final MethodVisitor mv = v.visitMethod(m.getName());
      if (mv != null) {
        m.visit(mv);
      }
    }
    v.end();
  }

  /**
   * Get method.
   * @param m Method name.
   * @return Method or null.
   */
  public Method getMethod(final MethodName m) {
    if (fMethods.containsKey(m)) {
      return fMethods.get(m);
    } else {
      return null;
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
   * Get access flags.
   * @return Access flags.
   */
  public int getAccessFlags() {
    return fAccessFlags;
  }
  
  /**
   * Get constant pool.
   * @return Constant pool.
   */
  public ConstantPool getConstantPool() {
    return fConstantPool;
  }
  
  /**
   * Get class name.
   * @return Name.
   */
  public ClassName getName() {
    return fName;
  }
  
  /**
   * Get superclass name.
   * @return Superclass name (possibly null).
   */
  public ClassName getSuperName() {
    return fSuperName;
  }
  
  /**
   * Get number of implemented interaces.
   * @return Number of implemented interfaces.
   */
  public int interfaceCount() {
    return fInterfaces.length;
  }
  
  /**
   * Get implemented interfaces.
   * @return Iterator.
   */
  public Iterator<ClassName> getInterfaces() {
    return new ArrayIterator<ClassName>(fInterfaces);
  }
  
  /**
   * Get number of fields.
   * @return Number of fields.
   */
  public int fieldCount() {
    return fFields.length;
  }
  
  /**
   * Get fields.
   * @return Iterator.
   */
  public Iterator<Field> getFields() {
    return new ArrayIterator<Field>(fFields);
  }

  /**
   * Get methods.
   * @return Iterator.
   */
  public Iterator<Method> getMethods() {
    return fMethods.values().iterator();
  }
    
  /**
   * Get all class attributes.
   * @return Iterator.
   */
  public Iterator<Attribute> getAttributes() {
    return fAttributes.iterator();
  }

  /**
   * Get writer.
   * @param os Output stream.
   * @return Writer.
   */
  public ClassVisitor getWriter(final OutputStream os) {
    return new DefaultWriter(this, os);
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
