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
  public void visitVoid() {
    internalName = "V";
    externalName = "void";
  }

  /** {@inheritDoc} */
  public void visitBoolean() {
    internalName = "Z";
    externalName = "boolean";
  }

  /** {@inheritDoc} */
  public void visitByte() {
    internalName = "B";
    externalName = "byte";
  }

  /** {@inheritDoc} */
  public void visitChar() {
    internalName = "C";
    externalName = "char";
  }

  /** {@inheritDoc} */
  public void visitDouble() {
    internalName = "D";
    externalName = "double";
  }

  /** {@inheritDoc} */
  public void visitFloat() {
    internalName = "F";
    externalName = "float";
  }

  /** {@inheritDoc} */
  public void visitInt() {
    internalName = "I";
    externalName = "int";
  }

  /** {@inheritDoc} */
  public void visitLong() {
    internalName = "J";
    externalName = "long";
  }

  /** {@inheritDoc} */
  public void visitShort() {
    internalName = "S";
    externalName = "short";
  }

  /** {@inheritDoc} */
  public void visitRefType(final String clazz) {
    internalName = "L" + clazz.replace('.', '/') + ";";
    externalName = clazz;
  }

  /** {@inheritDoc} */
  public void visitArray(final Type t) {
    t.accept(this);
    internalName = "[" + internalName;
    externalName = externalName + "[]";
  }

}
