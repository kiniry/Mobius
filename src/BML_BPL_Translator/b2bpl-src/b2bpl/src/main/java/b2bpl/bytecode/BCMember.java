package b2bpl.bytecode;


public abstract class BCMember implements Constants {

  protected final int accessModifiers;

  protected final JClassType owner;

  public BCMember(int accessModifiers, JClassType owner) {
    this.accessModifiers = accessModifiers;
    this.owner = owner;
  }

  public int getAccessModifiers() {
    return accessModifiers;
  }

  public JClassType getOwner() {
    return owner;
  }

  public boolean isPublic() {
    return (accessModifiers & ACC_PUBLIC) != 0;
  }

  public boolean isPrivate() {
    return (accessModifiers & ACC_PRIVATE) != 0;
  }

  public boolean isProtected() {
    return (accessModifiers & ACC_PROTECTED) != 0;
  }

  public boolean isPackageProtected() {
    return !(isPublic() || isPrivate() || isProtected());
  }

  public boolean isStatic() {
    return (accessModifiers & ACC_STATIC) != 0;
  }

  public boolean isFinal() {
    return (accessModifiers & ACC_FINAL) != 0;
  }
}
