package tests.loops;

public class Test2 {
    public void test2() {
    int j = 0;
    int[] tab = new int[17];
    /*@
    @ loop_invariant j <= 3;
    @*/
    for (int i: tab) {
      j++;
    }
  }
}
