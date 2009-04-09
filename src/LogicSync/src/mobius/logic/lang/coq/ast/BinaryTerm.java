
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package mobius.logic.lang.coq.ast;
import java.util.*;

import mobius.logic.lang.ast.FileLocation;

/** @author rgrig */
public class BinaryTerm extends Formula {


  private Formula next;
  private Formula op;
  private Formula left;
  private Formula right;




  // === Constructors and Factories ===
  protected BinaryTerm() {}
  private BinaryTerm(Formula next, Formula op, Formula left, Formula right) {
    this.location = FileLocation.unknown();
    this.next = next; 
    this.op = op; assert op != null;
    this.left = left; assert left != null;
    this.right = right; assert right != null;
  }

  private BinaryTerm(Formula next, Formula op, Formula left, Formula right, FileLocation location) {
    this(next,op,left,right);
    assert location != null;
    this.location = location;
  }
  
  public static BinaryTerm mk(Formula next, Formula op, Formula left, Formula right) {
    return new BinaryTerm(next, op, left, right);
  }

  public static BinaryTerm mk(Formula next, Formula op, Formula left, Formula right, FileLocation location) {
    return new BinaryTerm(next, op, left, right, location);
  }

  // === Accessors ===

  public Formula getNext() { return next; }
  public Formula getOp() { return op; }
  public Formula getLeft() { return left; }
  public Formula getRight() { return right; }

  public void setNext(Formula next) { this.next = next; }
  public void setOp(Formula op) { this.op = op; }
  public void setLeft(Formula left) { this.left = left; }
  public void setRight(Formula right) { this.right = right; }

  // === The Visitor pattern ===
  @Override
  public <R> R eval(Evaluator<R> evaluator) { 
    return evaluator.eval(this, next,op,left,right); 
  }

  // === Others ===
  @Override
  public BinaryTerm clone() {
    
      
        Formula newNext = next == null? 
          null : next.clone();
      
    
      
        Formula newOp = op == null? 
          null : op.clone();
      
    
      
        Formula newLeft = left == null? 
          null : left.clone();
      
    
      
        Formula newRight = right == null? 
          null : right.clone();
      
    
    return BinaryTerm.mk(newNext, newOp, newLeft, newRight, location);
  }
  
  public String toString() {
    return "[BinaryTerm " + 
                  next + " " + op + " " + left + " " + right + "]";
  }
}

