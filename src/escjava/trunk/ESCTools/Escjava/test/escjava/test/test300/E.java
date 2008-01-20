// Testing invariants - constructors and methods with bodies.

public class E {

  //@ invariant f>=99; 
  //@ invariant f/f == f/f; // divZero warning
  public int f;

  //@ invariant a.length>0; // null(a) warning
  public int [] a;

  /*@ normal_behavior
    @  requires ff>=99;
    @  requires a.length>0; //null(a) warning
    @  ensures this.f==ff;
    @  ensures this.a==a;
    @*/
  public E(int ff, int [] a) {
    this.f=ff;
    this.a=a;
  }

  /*@ ensures \result == this.f+1;
    @*/
  public int test0() {
    return this.f+1;
  } 

  /*@ requires ff>=99;
    @ ensures this.f == ff;
    @*/
  public int test1(int ff) {
    this.f=ff;
  }

}