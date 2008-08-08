package mobius.cct.classfile.types;

import java.io.EOFException;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;

import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.PackageName;

/**
 * Type of method result.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class ResultType {
  /**
   * Parse object type.
   * @param reader Input stream.
   * @return Parsed type.
   * @throws IOException .
   */
  private static ObjectType parseObject(final Reader reader) 
    throws IOException {
    final StringBuilder buf = new StringBuilder();
    int c;
    do {
      c = reader.read();
      if (c == -1) {
        throw new EOFException();
      }
      buf.append((char)c);
    } while (c != ';');
    final String[] name = buf.toString().split("/");
    if (name.length == 0) {
      throw new IllegalArgumentException();
    }
    PackageName pkg = PackageName.root();
    for (int i = 0; i < name.length - 1; i++) {
      pkg = PackageName.getPackage(pkg, name[i]);
    }
    final String cls0 = name[name.length - 1];
    final String cls = cls0.substring(0, cls0.length() - 1);
    return new ObjectType(new ClassName(pkg, cls));
  }
  
  // CHECKSTYLE:OFF
  /**
   * Parse type in internal form.
   * @param reader Input stream.
   * @return Parsed type.
   * @throws IOException . 
   */
  public static ResultType parse(final Reader reader) 
    throws IOException {

    final int c = reader.read();
    switch (c) {
      case 'L': 
        return parseObject(reader);
      case '[': 
        return new ArrayType(FieldType.parse(reader));
      case 'B': 
        return ByteType.getInstance();
      case 'C': 
        return CharType.getInstance();
      case 'D': 
        return DoubleType.getInstance();
      case 'F': 
        return FloatType.getInstance();
      case 'I': 
        return IntType.getInstance();
      case 'J': 
        return LongType.getInstance();
      case 'S': 
        return ShortType.getInstance();
      case 'Z': 
        return BooleanType.getInstance();
      case 'V':
        return VoidType.getInstance();
      case -1:
        throw new EOFException();
      default: 
        throw new IOException("Invalid character: " + 
                              Character.toString((char)c));
    } 
  }
  // CHECKSTYLE:ON
  
  /**
   * Parse result type in internal form.
   * @param str Input string.
   * @return Parsed type.
   * @throws IOException .
   */
  public static ResultType parse(final String str) 
    throws IOException {
    return parse(new StringReader(str));
  }
  
  /**
   * Encode type in a form suitable for inclusion in class file.
   * @return Internal form of type name.
   */
  public abstract String internalForm();
  
  /**
   * Encode type in a human-friendly form.
   * @return External form of type name.
   */
  public abstract String externalForm();
  
  /**
   * Check if type is void.
   * @return true iff this object represents void.
   */
  public abstract boolean isVoid();
  
  /**
   * Check if this type is a primitive type.
   * @return true iff this object represents a primitve type.
   */
  public abstract boolean isPrimitive();
  
  /**
   * Check if this type is an array type.
   * @return true iff this object represents an array type.
   */
  public abstract boolean isArray();

  /**
   * Check if this type is an object type.
   * @return true iff this object represents an object type.
   */
  public abstract boolean isObject();
}
