package b2bpl.bytecode;


public class BCField extends BCMember {

  public static final BCField[] EMPTY_ARRAY = new BCField[0];

  private final String name;

  private final JType type;

  private final String descriptor;

  private final boolean isGhostField;

  public BCField(
      int accessModifiers,
      JClassType owner,
      String name,
      JType type) {
    this(accessModifiers, owner, name, type, false);
  }

  public BCField(
      int accessModifiers,
      JClassType owner,
      String name,
      JType type,
      boolean isGhostField) {
    super(accessModifiers, owner);
    this.name = name;
    this.type = type;
    this.descriptor = type.getDescriptor();
    this.isGhostField = isGhostField;
  }

  public String getName() {
    return name;
  }

  public JType getType() {
    return type;
  }

  public String getDescriptor() {
    return descriptor;
  }

  public boolean isGhostField() {
    return isGhostField;
  }

  public String getQualifiedName() {
    return owner.getName() + "." + name;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(type.getName());
    sb.append(' ');
    sb.append(name);

    return sb.toString();
  }
}
