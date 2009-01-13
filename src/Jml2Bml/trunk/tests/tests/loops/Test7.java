package tests.loops;

public class Test7 {
  public void test7() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    do {
      j++;
    } while (j < 17);
  }
}
