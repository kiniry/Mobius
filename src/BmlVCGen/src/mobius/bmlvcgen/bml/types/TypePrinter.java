package mobius.bmlvcgen.bml.types;

/**
 * A type visitor which remembers name
 * of last visited type.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class TypePrinter implements ResultTypeVisitor {
  // Last type name in internal form.
  private String internalName;
  // Last type name in external form.
  private String externalName;
  
  /**
   * Get internal name of last type visited.
   * @return Type name.
   */
  public String getInternalName() {
    return internalName;
  }

  /**
   * Get external name of last type visited.
   * @return Type name.
   */
  public String getExternalName() {
    return externalName;
  }
  
  /** {@inheritDoc} */
  @Override
  public void visitVoid() {
    internalName = "V";
    externalName = "void";
  }

  /** {@inheritDoc} */
  @Override
  public void visitBoolean() {
    internalName = "Z";
    externalName = "boolean";
  }

  /** {@inheritDoc} */
  @Override
  public void visitByte() {
    internalName = "B";
    externalName = "byte";
  }

  /** {@inheritDoc} */
  @Override
  public void visitChar() {
    internalName = "C";
    externalName = "char";
  }

  /** {@inheritDoc} */
  @Override
  public void visitDouble() {
    internalName = "D";
    externalName = "double";
  }

  /** {@inheritDoc} */
  @Override
  public void visitFloat() {
    internalName = "F";
    externalName = "float";
  }

  /** {@inheritDoc} */
  @Override
  public void visitInt() {
    internalName = "I";
    externalName = "int";
  }

  /** {@inheritDoc} */
  @Override
  public void visitLong() {
    internalName = "J";
    externalName = "long";
  }

  /** {@inheritDoc} */
  @Override
  public void visitShort() {
    internalName = "S";
    externalName = "short";
  }

  /** {@inheritDoc} */
  @Override
  public void visitRefType(final String clazz) {
    internalName = "L" + clazz.replace('.', '/') + ";";
    externalName = clazz;
  }

  /** {@inheritDoc} */
  @Override
  public void visitArray(final Type t) {
    t.accept(this);
    internalName = "[" + internalName;
    externalName = externalName + "[]";
  }

}
