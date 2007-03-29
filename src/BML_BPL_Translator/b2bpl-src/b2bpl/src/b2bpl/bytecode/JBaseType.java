package b2bpl.bytecode;


public class JBaseType extends JType {

  public static final JBaseType BOOLEAN = new JBaseType("boolean", "Z");

  public static final JBaseType BYTE = new JBaseType("byte", "B");

  public static final JBaseType CHAR = new JBaseType("char", "C");

  public static final JBaseType DOUBLE = new JBaseType("double", "D");

  public static final JBaseType FLOAT = new JBaseType("float", "F");

  public static final JBaseType INT = new JBaseType("int", "I");

  public static final JBaseType LONG = new JBaseType("long", "J");

  public static final JBaseType SHORT = new JBaseType("short", "S");

  public static final JBaseType VOID = new JBaseType("void", "V");

  private final String name;

  private final String descriptor;

  private JBaseType(String name, String descriptor) {
    this.name = name;
    this.descriptor = descriptor;
  }

  public String getName() {
    return name;
  }

  public int getSize() {
    return (equals(LONG) || equals(DOUBLE)) ? 2 : 1;
  }

  public String getDescriptor() {
    return descriptor;
  }

  public boolean isBaseType() {
    return true;
  }

  public boolean isSubtypeOf(JType type) {
    return equals(type);
  }

  public String toString() {
    return name;
  }
}
