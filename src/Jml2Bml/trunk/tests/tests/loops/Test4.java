package tests.loops;

public class Test4 {
  public void test4() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    while (true) {
      j++;
    }
  }
}
