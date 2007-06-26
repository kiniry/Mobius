//@ model import org.jmlspecs.models.*;
public abstract class UnboundedStack {

  /*@ public model JMLObjectSequence theStack;
    @ public initially theStack != null
    @                  && theStack.isEmpty();
    @*/

  //@ public invariant theStack != null;

  /*@ public normal_behavior
    @   requires !theStack.isEmpty();
    @   assignable theStack;
    @   ensures theStack.equals(
    @              \old(theStack.trailer()));
    @*/
  public abstract void pop( );

  /*@ public normal_behavior
    @   assignable theStack;
    @   ensures theStack.equals(
    @              \old(theStack.insertFront(x)));
    @*/
  public abstract void push(Object x);

  /*@ public normal_behavior
    @   requires !theStack.isEmpty();
    @   assignable \nothing;
    @   ensures \result == theStack.first();
    @*/
  public /*@ pure @*/ abstract Object top( );
}
