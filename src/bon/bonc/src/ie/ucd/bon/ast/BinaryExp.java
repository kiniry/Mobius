
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class BinaryExp extends Expression {
  public static enum Op {
    EQUIV, 
    GE, 
    HASTYPE, 
    LT, 
    NEQ, 
    XOR, 
    IMPLIES, 
    POW, 
    NOTMEMBEROF, 
    MOD, 
    INTDIV, 
    OR, 
    MEMBEROF, 
    GT, 
    SUB, 
    EQ, 
    DIV, 
    AND, 
    MUL, 
    LE, 
    ADD
  }

  private final Expression left;
  private final Expression right;

  private final Op op;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected BinaryExp(Op op, Expression left, Expression right) {
    this(op,left,right, null);    
  }

  protected BinaryExp(Op op, Expression left, Expression right, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.op = op; 
    this.left = left; assert left != null;
    this.right = right; assert right != null;
    
  }
  
  public static BinaryExp mk(Op op, Expression left, Expression right) {
    return new BinaryExp(op, left, right);
  }

  public static BinaryExp mk(Op op, Expression left, Expression right, SourceLocation location) {
    return new BinaryExp(op, left, right, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public Op getOp() { return op; }
  public Expression getLeft() { return left; }
  public Expression getRight() { return right; }

  // === Others ===
  @Override
  public BinaryExp clone() {
    Op newOp = op;
    Expression newLeft = left == null ? null : left.clone();
    Expression newRight = right == null ? null : right.clone();
    
    return BinaryExp.mk(newOp, newLeft, newRight, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("BinaryExp ast node: ");
    
    sb.append("op = ");
    sb.append(op);
    sb.append(", ");
    
    sb.append("left = ");
    sb.append(left);
    sb.append(", ");
    
    sb.append("right = ");
    sb.append(right);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

