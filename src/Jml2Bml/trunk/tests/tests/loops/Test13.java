package tests.loops;

public class Test13 {
  public void test13() {
    try {
      for (int i = 0; i < 12; i++)
        if (i > 10)
          throw new Exception();
    } catch (Exception e) {
      for (int j = 0; j < 12; j++)
        if (j > 11)
          throw new RuntimeException();
    }
  }
}
