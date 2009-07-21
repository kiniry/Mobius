package b2bpl.bytecode;

import java.util.ArrayList;
import java.util.List;


public abstract class JType {

  public boolean isBaseType() {
    return false;
  }

  public boolean isReferenceType() {
    return false;
  }

  public boolean isClassType() {
    return false;
  }

  public boolean isArrayType() {
    return false;
  }

  public abstract String getName();

  public String getInternalName() {
    return getName();
  }

  public int getSize() {
    return 1;
  }

  public final boolean isCategory1CompType() {
    return getSize() == 1;
  }

  public abstract boolean isSubtypeOf(JType type);

  public final boolean isProperSubtypeOf(JType type) {
    return isSubtypeOf(type) && !equals(type);
  }

  public static JType fromDescriptor(String descriptor) {
    return fromDescriptor(descriptor.toCharArray(), 0);
  }

  public String getDescriptor() {
    return null;
  }

  private static JType fromDescriptor(char[] descriptor, int offset) {
    switch (descriptor[offset]) {
      case 'B':
        return JBaseType.BYTE;
      case 'C':
        return JBaseType.CHAR;
      case 'D':
        return JBaseType.DOUBLE;
      case 'F':
        return JBaseType.FLOAT;
      case 'I':
        return JBaseType.INT;
      case 'J':
        return JBaseType.LONG;
      case 'S':
        return JBaseType.SHORT;
      case 'V':
        return JBaseType.VOID;
      case 'Z':
        return JBaseType.BOOLEAN;
      case 'L':
        int end = offset + 1;
        while ((end < descriptor.length) && (descriptor[end] != ';')) {
          end++;
        }
        if (end == descriptor.length) {
          break;
        }
        String name = new String(descriptor, offset + 1, end - (offset + 1));
        return TypeLoader.getClassType(name);
      case '[':
        int dimension = 0;
        while ((offset < descriptor.length) && (descriptor[offset] == '[')) {
          dimension++;
          offset++;
        }
        if (offset == descriptor.length) {
          break;
        }
        JType elementType = fromDescriptor(descriptor, offset);
        if (elementType == JBaseType.VOID) {
          break;
        }
        return new JArrayType(elementType, dimension);
    }

    // TODO[om]: Throw some exception!
    return null;
  }

  public static JType[] fromMethodDescriptor(String descriptor) {
    List<JType> types = new ArrayList<JType>();

    int offset = 1;
    while (descriptor.charAt(offset) != ')') {
      String typeDescriptor = extractDescriptor(descriptor, offset);
      types.add(fromDescriptor(typeDescriptor));
      offset += typeDescriptor.length();
    }

    String typeDescriptor = extractDescriptor(descriptor, offset + 1);
    types.add(fromDescriptor(typeDescriptor));

    return types.toArray(new JType[types.size()]);
  }

  public static JType[] argumentTypes(String descriptor) {
    JType[] types = fromMethodDescriptor(descriptor);
    JType[] argumentTypes = new JType[types.length - 1];
    System.arraycopy(types, 0, argumentTypes, 0, argumentTypes.length);
    return argumentTypes;
  }

  public static JType returnType(String descriptor) {
    JType[] types = fromMethodDescriptor(descriptor);
    return types[types.length - 1];
  }

  private static String extractDescriptor(String buffer, int offset) {
    String descriptor = null;

    int end = offset;
    while ((end < buffer.length()) && (buffer.charAt(end) == '[')) {
      end++;
    }
    if (end < buffer.length()) {
      switch (buffer.charAt(end)) {
        case 'B':
        case 'C':
        case 'D':
        case 'F':
        case 'I':
        case 'J':
        case 'S':
        case 'V':
        case 'Z':
          descriptor = buffer.substring(offset, end + 1);
          break;
        case 'L':
          end = buffer.indexOf(';', end);
          if (end >= 0) {
            descriptor = buffer.substring(offset, end + 1);
          }
          break;
      }
    }

    return descriptor;
  }

  public static String computeMethodDescriptor(
      JType returnType,
      JType[] parameterTypes) {
    StringBuffer sb = new StringBuffer();

    sb.append('(');
    for (int i = 0; i < parameterTypes.length; i++) {
      sb.append(parameterTypes[i].getDescriptor());
    }
    sb.append(')');
    sb.append(returnType.getDescriptor());

    return sb.toString();
  }
}
