package mobius.cct.classfile;

import java.io.DataInputStream;
import java.io.IOException;

import mobius.cct.classfile.types.FieldType;
import mobius.cct.constantpool.ConstantPool;
import mobius.cct.constantpool.DefaultPool;
import mobius.cct.repositories.InvalidFormatException;

/**
 * Field in a class file.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class Field {
  // ACCESS FLAGS.
  /** 
   *  Declared public; may be accessed from outside its package.
   */
  public static final int ACC_PUBLIC = 0x0001; 
  /** 
   *  Declared private; usable only within the deﬁning class.
   */
  public static final int ACC_PRIVATE = 0x0002; 
  /** 
   *  Declared protected; may be accessed within subclasses.
   */
  public static final int ACC_PROTECTED = 0x0004; 
  /** 
   *  Declared static.
   */
  public static final int ACC_STATIC = 0x0008; 
  /** 
   *  Declared final; no further assignment after initialization.
   */
  public static final int ACC_FINAL = 0x0010; 
  /** 
   *  Declared volatile; cannot be cached. 
   */
  public static final int ACC_VOLATILE = 0x0040; 
  /** 
   *  Declared transient; not written or read 
   *  by a persistent object manager.
   */
  public static final int ACC_TRANSIENT = 0x0080; 
  /** 
   *  Declared synthetic; Not present in the source code.
   */
  public static final int ACC_SYNTHETIC = 0x1000; 
  /** 
   *  Declared as an element of an enum.
   */
  public static final int ACC_ENUM = 0x4000; 

  /**
   * Access flags.
   */
  private final int fAccessFlags;
  
  /**
   * Name.
   */
  private final String fName;
  
  /**
   * Type descriptor.
   */
  private final FieldType fType;
  
  /**
   * Attributes.
   */
  private final AttributeMap fAttributes;
  
  /**
   * Constructor - read field from a stream.
   * @param ds Input stream.
   * @param cp Constant pool.
   * @throws IOException .
   */
  public Field(final DataInputStream ds,
               final ConstantPool cp) throws IOException {
    fAccessFlags = ds.readUnsignedShort();
    final int nameIndex = ds.readUnsignedShort();
    fName = DefaultPool.getString(cp, nameIndex);
    if (fName == null) {
      throw new InvalidFormatException("Invalid field name.");
    }
    final int typeIndex = ds.readUnsignedShort();
    final String type = DefaultPool.getString(cp, typeIndex);
    if (type == null) {
      throw new InvalidFormatException("Invalid field type.");
    }
    fType = FieldType.parse(type);
    fAttributes = new AttributeMap(ds, cp);
  }
  
  /**
   * Get access flags.
   * @return Access flags.
   */
  public int getAccessFlags() {
    return fAccessFlags;
  }
  
  /**
   * Get name.
   * @return Name.
   */
  public String getName() {
    return fName;
  }
  
  /**
   * Get type.
   * @return Type.
   */
  public FieldType getType() {
    return fType;
  }
  
  /**
   * Access attributes.
   * @return Attributes.
   */
  public AttributeMap getAttributes() {
    return fAttributes;
  }
}
