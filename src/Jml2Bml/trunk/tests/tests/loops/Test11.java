package tests.loops;

public class Test11 {
  public void test11() {
    int i = 0;
    outer: while (true) {
      i++;
      for (int j = 0; j < 13; j++) {
        if (j > 12 && i < j)
          break outer;
      }
    }
  }
}
