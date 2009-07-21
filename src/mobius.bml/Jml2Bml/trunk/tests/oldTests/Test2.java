package oldTests;

public class Test2 {
  public Test2 parent = new Test2();
  public String abc = null;
  public String efg = null;
  public int ab  = 12;
  private String ala = null;
  //@ requires ala == null;
  //@ ensures \result < \old(ala);
  //@ signals (java.lang.Exception) 2 < 0;
  //@ signals (Exception) false;
  public int abc(){
    //@ ghost String x = null;
    //@ assert x < 11;
    //@ assert ala < 123;
    return 17;
  }

}
