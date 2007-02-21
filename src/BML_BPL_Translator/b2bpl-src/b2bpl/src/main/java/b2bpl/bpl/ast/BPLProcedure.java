package b2bpl.bpl.ast;

import b2bpl.bpl.BPLVisitor;


public class BPLProcedure extends BPLDeclaration {

  private final String name;

  private final BPLVariable[] inParameters;

  private final BPLVariable[] outParameters;

  private final BPLSpecification specification;

  private final BPLImplementationBody body;

  public BPLProcedure(
      String name,
      BPLVariable[] inParameters,
      BPLVariable[] outParameters,
      BPLSpecification specification) {
    this(name, inParameters, outParameters, specification, null);
  }

  public BPLProcedure(
      String name,
      BPLVariable[] inParameters,
      BPLVariable[] outParameters,
      BPLSpecification specification,
      BPLImplementationBody body) {
    this.name = name;
    this.inParameters = inParameters;
    this.outParameters = outParameters;
    this.specification = specification;
    this.body = body;
  }

  public String getName() {
    return name;
  }

  public BPLVariable[] getInParameters() {
    return inParameters;
  }

  public BPLVariable[] getOutParameters() {
    return outParameters;
  }

  public BPLSpecification getSpecification() {
    return specification;
  }

  public BPLImplementationBody getBody() {
    return body;
  }

  public <R> R accept(BPLVisitor<R> visitor) {
    return visitor.visitProcedure(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append("procedure ");
    sb.append(name);
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
    if (body == null) {
      sb.append(';');
    }
    sb.append(System.getProperty("line.separator"));
    if (specification != null) {
      for (BPLSpecificationClause clause : specification.getClauses()) {
        sb.append("  ");
        sb.append(clause);
        sb.append(System.getProperty("line.separator"));
      }
    }
    if (body != null) {
      sb.append('{');
      sb.append(System.getProperty("line.separator"));
      sb.append(body);
      sb.append('}');
    }

    return sb.toString();
  }
}
