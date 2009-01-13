package tests.loops;

public class Test6 {
  public void test6() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    do {
      j++;
    } while (true);
  }
}
