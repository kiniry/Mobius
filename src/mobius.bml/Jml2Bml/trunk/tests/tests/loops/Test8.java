package tests.loops;

public class Test8 {
  public void test8() {
    int k = 0;
    /*@
    @ loop_invariant k <= 3;
    @*/
    for (int i = 0; i < 13; i++) {
      /*@
      @ loop_invariant k <= 4;
      @*/
      for (int j = 0; j < 15; j++)
        k++;
    }
  }
}
