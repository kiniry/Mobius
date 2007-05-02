package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLFunctionApplication extends BPLExpression {

  private final String functionName;

  private final BPLExpression[] arguments;

  private BPLFunction function;

  public BPLFunctionApplication(
      String functionName,
      BPLExpression... arguments) {
    super(Precedence.ATOM);
    this.functionName = functionName;
    this.arguments = arguments;
  }

  public String getFunctionName() {
    return functionName;
  }

  public BPLExpression[] getArguments() {
    return arguments;
  }

  public BPLFunction getFunction() {
    return function;
  }

  public void setFunction(BPLFunction function) {
    this.function = function;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitFunctionApplication(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(functionName);
    sb.append('(');
    for (int i = 0; i < arguments.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(arguments[i]);
    }
    sb.append(')');

    return sb.toString();
  }
}
