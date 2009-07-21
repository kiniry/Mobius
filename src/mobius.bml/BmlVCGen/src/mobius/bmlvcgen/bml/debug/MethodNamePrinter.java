package mobius.bmlvcgen.bml.debug;

import mobius.bmlvcgen.bml.MethodNameVisitor;
import mobius.bmlvcgen.bml.types.ResultType;
import mobius.bmlvcgen.bml.types.Type;
import mobius.bmlvcgen.bml.types.TypePrinter;

/**
 * Method name visitor which converts method
 * name and type to a string.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class MethodNamePrinter implements MethodNameVisitor {
  private final StringBuilder builder;
  // Object used to convert types to strings.
  private final TypePrinter typePrinter;
  // Last method name.
  private String lastName;
  // Flag set after visiting first argument.
  private boolean argFlag;
  
  /**
   * Constructor.
   */
  public MethodNamePrinter() {
    typePrinter = new TypePrinter();
    builder = new StringBuilder();
  }
  
  /** {@inheritDoc} */
  public void visitName(final String name) {
    builder.delete(0, builder.length());
    lastName = name;
  }

  /** {@inheritDoc} */
  public void visitResultType(final ResultType t) {
    t.accept(typePrinter);
    builder.append(typePrinter.getExternalName());
    builder.append(" ");
    builder.append(lastName);
  }

  /** {@inheritDoc} */
  public void beginArgs() {
    builder.append("(");
    argFlag = false;
  }

  /** {@inheritDoc} */
  public void visitArg(final Type t, final String name) {
    if (argFlag) {
      builder.append(", ");
    }
    t.accept(typePrinter);
    builder.append(typePrinter.getExternalName());
    if (name != null) {
      // TODO: Argument name does not match bml name.
      builder.append(" ");
      builder.append(name);
    }
    argFlag = true;
  }

  /** {@inheritDoc} */
  public void endArgs() {
    builder.append(")");
  }

  /**
   * Get text representation of last method name
   * visited by this object.
   * @return String.
   */
  public String getText() {
    return builder.toString();
  }
  
  /**
   * Get name of last visited method.
   * @return Name.
   */
  public String getName() {
    return lastName;
  }
  
}
