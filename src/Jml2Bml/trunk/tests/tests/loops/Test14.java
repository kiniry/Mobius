package tests.loops;

public class Test14 {
  public void test14() {
    try {
      for (int i = 0; i < 12; i++)
        if (i > 10)
          throw new Exception();
    } catch (Exception e) {
      for (int j = 0; j < 12; j++)
        if (j > 10)
          break;
    } finally {
      int j = 0;
      while (j < 12)
        j++;
    }

  }
}
