package tests.loops;

public class Test9 {
  public void test9() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    while (true) {
      j++;
      if (j > 12)
        break;
    }
  }
}
