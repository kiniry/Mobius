package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLImplementation extends BPLDeclaration {

  private final String procedureName;

  private final BPLVariable[] inParameters;

  private final BPLVariable[] outParameters;

  private final BPLImplementationBody body;

  private BPLProcedure procedure;

  public BPLImplementation(
      String procedureName,
      BPLVariable[] inParameters,
      BPLVariable[] outParameters,
      BPLImplementationBody body) {
    this.procedureName = procedureName;
    this.inParameters = inParameters;
    this.outParameters = outParameters;
    this.body = body;
  }

  public String getProcedureName() {
    return procedureName;
  }

  public BPLVariable[] getInParameters() {
    return inParameters;
  }

  public BPLVariable[] getOutParameters() {
    return outParameters;
  }

  public BPLImplementationBody getBody() {
    return body;
  }
  
  public BPLProcedure getProcedure() {
    return procedure;
  }

  public void setProcedure(BPLProcedure procedure) {
    this.procedure = procedure;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitImplementation(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("implementation ");
    sb.append(procedureName);
    sb.append('(');
    for (int i = 0; i < inParameters.length; i++) {
      if (i > 0) {
        sb.append(", ");
      }
      sb.append(inParameters[i]);
    }
    sb.append(')');
    if (outParameters.length > 0) {
      sb.append(" returns ");
      sb.append('(');
      for (int i = 0; i < outParameters.length; i++) {
        if (i > 0) {
          sb.append(", ");
        }
        sb.append(outParameters[i]);
      }
      sb.append(')');
    }
    sb.append(System.getProperty("line.separator"));
    sb.append('{');
    sb.append(System.getProperty("line.separator"));
    sb.append(body);
    sb.append('}');

    return sb.toString();
  }
}
