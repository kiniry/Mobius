package tests.loops;

public class Test1 {
  public void method() {
    int j = 0;
    /*@
     @ loop_invariant j <= 3;
     @*/
    for (int i = 0; i < 2; i++) {
      j++;
    }
  }
}
