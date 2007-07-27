package b2bpl.bytecode;


public class JNullType extends JReferenceType {

  public static final JNullType NULL = new JNullType();

  private JNullType() {
    // hide the constructor
  }

  public String getName() {
    return "null";
  }

  public boolean isSubtypeOf(JType type) {
    return type.isReferenceType();
  }
}
