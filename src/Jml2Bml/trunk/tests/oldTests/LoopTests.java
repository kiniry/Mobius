package oldTests;

public class LoopTests {

  public void test01() {
    int j = 0;
    /*@
     @ loop_invariant j <= 3;
     @*/
    for (int i = 0; i < 2; i++) {
      j++;
    }
  }

  public void test02() {
    int j = 0;
    int[] tab = new int[17];
    /*@
    @ loop_invariant j <= 3;
    @*/
    for (int i : tab) {
      j++;
    }
  }

  public void test03() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    for (;;) { //while true
      j++;
    }
  }

  public void test04() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    while (true) {
      j++;
    }
  }

  public void test05() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    while (j < 15) {
      j++;
    }
  }

  public void test06() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    do {
      j++;
    } while (true);
  }

  public void test07() {
    int j = 0;
    /*@
    @ loop_invariant j <= 3;
    @*/
    do {
      j++;
    } while (j < 17);
  }

  public void test08() {
    int k = 0;
    /*@
    @ loop_invariant k <= 3;
    @*/
    for (int i = 0; i < 13; i++) {
      /*@
      @ loop_invariant k <= 3;
      @*/
      for (int j = 0; j < 15; j++)
        k++;
    }
  }

  public void test09() {
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

  public void test10() {
    int j = 0;
    /*@
      @ loop_invariant j <= 3;
      @*/
    while (true) {
      j++;
      if (j < 13)
        continue;
    }
  }

  public void test11() {
    int i = 0;
    outer:
    /*@
    @ loop_invariant i <= 3;
    @*/
    while (true) {
      i++;
      /*@
      @ loop_invariant i <= 3;
      @*/
      for (int j = 0; j < 13; j++) {
        if (j > 12 && i < j)
          break outer;
      }
    }
  }

  public void test12() {
    int i = 0;
    /*@
    @ loop_invariant i <= 3;
    @*/
    for (i = 0; i < 100; i++) {
      inner:
      /*@
      @ loop_invariant i <= 3;
      @*/
      for (int j = 0; j < 100; j++) {
        /*@
        @ loop_invariant j <= 3;
        @*/
        for (int k = 0; k < 100; k++)
          if (i > 12 && j > 12 && k > 12)
            break inner;
      }
      if (i < 13)
        break;
    }
  }

  public void test13() {
    try {
      int i = 0;
      /*@
      @ loop_invariant i <= 3;
      @*/
      for (i = 0; i < 12; i++)
        if (i > 10)
          throw new Exception();
    } catch (Exception e) {
      int j = 0;
      /*@
      @ loop_invariant j <= 3;
      @*/
      for (j = 0; j < 12; j++)
        if (j > 10)
          throw new RuntimeException();
    }
  }

  public void test14() {
    try {
      int i = 0;
      for (i = 0; i < 12; i++)
        if (i > 10)
          throw new Exception();
    } catch (Exception e) {
      int j = 0;
      for (j = 0; j < 12; j++)
        if (j > 10)
          break;
    } finally {
      int j = 0;
      /*@
      @ loop_invariant j <= 3;
      @*/
      while (j < 12)
        j++;
    }

  }

  public void test15() {
    int z = 0;
    a:
    /*@
    @ loop_invariant z <= 3;
    @*/
    for (int i = 0; i < 12; i++) {
      b:
      /*@
      @ loop_invariant i <= 3;
      @*/
      for (int j = 0; j < 12; j++) {
        c:
        /*@
        @ loop_invariant j <= 3;
        @*/
        for (int k = 0; k < 12; k++) {
          /*@
          @ loop_invariant k <= 3;
          @*/
          for (int l = 0; l < 12; l++)
            if (k < l)
              break b;
          if (j > k)
            break a;
        }
      }
    }
  }

  public void test16() {
    try {
      int i = 0;
    } finally {
      int k = 0;
      int j = 0;
      /*@
      @ loop_invariant j <= 3;
      @*/
      for (j = 0; j < 12; j++) {
        k++;
      }
    }

  }

  public void test17() {
    int j = 0;
    if (j < 0) {
      j = 17;
    } else {
      /*@
      @ loop_invariant j <= 3;
      @*/
      do {
        j++;
      } while (j < 12);
    }
  }
}
