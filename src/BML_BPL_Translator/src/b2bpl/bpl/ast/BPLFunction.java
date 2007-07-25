package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLFunction extends BPLDeclaration {

  private final String[] names;

  private final BPLFunctionParameter[] inParameters;

  private final BPLFunctionParameter outParameter;

  public BPLFunction(
      String name,
      BPLFunctionParameter[] inParameters,
      BPLFunctionParameter outParameter) {
    this(new String[] { name }, inParameters, outParameter);
  }

  public BPLFunction(
      String[] names,
      BPLFunctionParameter[] inParameters,
      BPLFunctionParameter outParameter) {
    this.names = names;
    this.inParameters = inParameters;
    this.outParameter = outParameter;
  }

  public String[] getNames() {
    return names;
  }

  public BPLFunctionParameter[] getInParameters() {
    return inParameters;
  }

  public BPLFunctionParameter getOutParameter() {
    return outParameter;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitFunction(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("function ");
    for (int i = 0; i < names.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(names[i]);
    }
    sb.append('(');
    for (int i = 0; i < inParameters.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(inParameters[i]);
    }
    sb.append(')');
    if (outParameter != null) {
      sb.append(" returns ");
      sb.append('(');
      sb.append(outParameter);
      sb.append(')');
    }
    sb.append(';');

    return sb.toString();
  }
}
