
/**
 * Copyright (c) 2007-2010, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from normal_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

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

  public final Expression left;
  public final Expression right;

  public final Op op;


  // === Constructors and Factories ===
  protected BinaryExp(Op op, Expression left, Expression right, SourceLocation location) {
    super(location);
    this.op = op; 
    this.left = left; assert left != null;
    this.right = right; assert right != null;
  }

  public static BinaryExp mk(Op op, Expression left, Expression right, SourceLocation location) {
    return new BinaryExp(op, left, right, location);
  }

  // === Accessors ===

  public Op getOp() { return op; }
  public Expression getLeft() { return left; }
  public Expression getRight() { return right; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitBinaryExp(this, op, left, right, getLocation());
  }

  // === Others ===
  @Override
  public BinaryExp clone() {
    Op newOp = op;
    Expression newLeft = left == null ? null : left.clone();
    Expression newRight = right == null ? null : right.clone();
    return BinaryExp.mk(newOp, newLeft, newRight, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

