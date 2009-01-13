package tests.loops;

public class Test12 {
  public void test12() {
    for (int i = 0; i < 100; i++) {
      inner: for (int j = 0; j < 100; j++)
        for (int k = 0; k < 100; k++)
          if (i > 12 && j > 12 && k > 12)
            break inner;
      if (i < 13)
        break;
    }
  }
}
