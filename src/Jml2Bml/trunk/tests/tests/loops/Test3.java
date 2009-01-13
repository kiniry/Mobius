package tests.loops;

public class Test3 {
    public void test3() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    for (;;) {
      j++;
    }
  }
}
