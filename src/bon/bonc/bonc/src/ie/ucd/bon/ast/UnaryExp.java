
/**
  This class is generated automatically from normal_classes.tpl.
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class UnaryExp extends Expression {
  public static enum Op {
    OLD, 
    DELTA, 
    SUB, 
    NOT, 
    ADD
  }

  public final Expression expression;

  public final Op op;


  // === Constructors and Factories ===
  protected UnaryExp(Op op, Expression expression, SourceLocation location) {
    super(location);
    this.op = op; 
    this.expression = expression; assert expression != null;
  }

  public static UnaryExp mk(Op op, Expression expression, SourceLocation location) {
    return new UnaryExp(op, expression, location);
  }

  // === Accessors ===

  public Op getOp() { return op; }
  public Expression getExpression() { return expression; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitUnaryExp(this, op, expression, getLocation());
  }

  // === Others ===
  @Override
  public UnaryExp clone() {
    Op newOp = op;
    Expression newExpression = expression == null ? null : expression.clone();
    return UnaryExp.mk(newOp, newExpression, getLocation());
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("UnaryExp ast node: ");
    sb.append("op = ");
    sb.append(op);
    sb.append(", ");
        sb.append("expression = ");
    sb.append(expression);
    sb.append(", ");
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }
}

