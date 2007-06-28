public abstract class ValidForEx {
  //@ public ghost Class validFor = null;

  private /*@ spec_public @*/ int x;

  //@ public invariant validFor <: \type(ValidForEx) ==> x > 3;

  public int getX() { return x; }

  //@ requires validFor == \type(ValidForEx) && v > 3;
  //@ assignable x, validFor;
  //@ ensures validFor == \type(ValidForEx) && x == v;
  public void setX(int v) {
    //@ set validFor = \type(Object);
    x = v;
    //@ assert x > 3;
    //@ set validFor = \type(ValidForEx);
  }
}
