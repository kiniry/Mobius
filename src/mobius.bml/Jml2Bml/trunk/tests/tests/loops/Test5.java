package tests.loops;

public class Test5 {
  public void test5() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    while (j < 15) {
      j++;
    }
  }
}
