package b2bpl.bpl.ast;

import b2bpl.bpl.IBPLVisitor;


public class BPLVariable extends BPLNode {

  public static final BPLVariable[] EMPTY_ARRAY = new BPLVariable[0];

  private String name;

  private BPLType type;

  private final BPLExpression whereClause;

  public BPLVariable(String name, BPLType type) {
    this(name, type, null);
  }

  public BPLVariable(String name, BPLType type, BPLExpression whereClause) {
    this.name = name;
    this.type = type;
    this.whereClause = whereClause;
  }

  public String getName() {
    return name;
  }

  public BPLType getType() {
    return type;
  }
  
  public void setName(String value) {
    name = value;
  }
  
  public void setType(BPLType value) {
    type = value;
  }

  public BPLExpression getWhereClause() {
    return whereClause;
  }

  public <R> R accept(IBPLVisitor<R> visitor) {
    return visitor.visitVariable(this);
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(name);
    sb.append(": ");
    sb.append(type);
    if (whereClause != null) {
      sb.append(" where ");
      sb.append(whereClause);
    }

    return sb.toString();
  }
}
