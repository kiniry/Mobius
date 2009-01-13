package tests.loops;

public class Test15 {
  public void test15() {
    a: for (int i = 0; i < 12; i++)
      b: for (int j = 0; j < 12; j++)
        c: for (int k = 0; k < 12; k++) {
          for (int l = 0; l < 12; l++)
            if (k < l)
              break b;
          if (j > k)
            break a;
        }
  }
}
