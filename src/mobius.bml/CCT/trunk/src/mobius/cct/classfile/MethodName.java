package mobius.cct.classfile;

import java.io.IOException;
import java.util.Iterator;

import mobius.cct.classfile.types.FieldType;


/**
 * Method name with types of arguments and result.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class MethodName implements Comparable<MethodName> {
  /**
   * Type.
   */
  private final MethodType fType;
  
  /**
   * Name.
   */
  private final String fName;
  
  /**
   * Cached hashcode.
   */
  private final int fHash;
  
  /**
   * Constructor.
   * @param name Method name.
   * @param type Method type.
   */
  public MethodName(final String name, 
                    final MethodType type) {
    fName = name;
    fType = type;
    fHash = internalForm().hashCode();
  }
  
  /**
   * Create method with given name and encoded type. If the type
   * is invalid, null is returned.
   * @param name Method name.
   * @param type Encoded type (like "(IIB)V").
   * @return MethodName instance.
   */
  public static MethodName get(final String name, final String type) {
    try {
      final MethodType methodType = MethodType.parse(type);
      return new MethodName(name, methodType);
    } catch (IOException e) {
      return null;
    }
  }
  
  /**
   * Get method type.
   * @return Type.
   */
  public MethodType getType() {
    return fType;
  }
  
  /**
   * Get method name.
   * @return Name.
   */
  public String getName() {
    return fName;
  }
  
  /**
   * Encode method name and type in internal form.
   * @return Encoded method name and type.
   */
  public String internalForm() {
    final StringBuilder sb = new StringBuilder();
    sb.append(fName);
    sb.append('(');
    final Iterator<FieldType> i = fType.getArgs();
    while (i.hasNext()) {
      sb.append(i.next().internalForm());
    }
    sb.append(')');
    sb.append(fType.getResult().internalForm());
    return sb.toString();
  }
  
  /**
   * Encode method name and type in external form.
   * @return Encoded method name and type.
   */
  public String externalForm() {
    final StringBuilder sb = new StringBuilder();
    
    sb.append(fType.getResult().externalForm());
    sb.append(' ');
    sb.append(fName);
    sb.append('(');
    final Iterator<FieldType> i = fType.getArgs();
    while (i.hasNext()) {
      sb.append(i.next().externalForm());
      if (i.hasNext()) {
        sb.append(", ");
      }
    }
    sb.append(')');
    return sb.toString();
  }

  /**
   * Hashcode.
   * @return hashcode.
   */
  @Override
  public int hashCode() {
    return fHash;
  }
  
  /**
   * Compare method names.
   * @param m Method name.
   * @return .
   */
  public int compareTo(final MethodName m) {
    return internalForm().compareTo(m.internalForm());
  }
  
  /**
   * Equals.
   * @param obj Object to compare.
   * @return .
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    }
    if (obj.getClass().equals(this.getClass())) {
      return compareTo((MethodName)obj) == 0;
    } else {
      return obj.equals(this);
    }
  }
  
}
