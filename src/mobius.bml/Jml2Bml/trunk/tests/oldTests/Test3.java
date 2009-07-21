package oldTests;

public class Test3 {
  public static void main(String[] args) {
    String d = "";
    System.out.println(d);
    for (int i = 0; i < 10; i++) {
      double x = 2 / 3;
      x += 1;
      for (int j = 0; j < i; j++) {
        x = i - j;
        int k = 0;
        while (k < i + j) {
          k++;
          k = i + j;
        }
      }
    }
    int i = 0;
    while (true) {
      i++;
      if (i > 5) {
        System.out.println(i);
      }
    }
  }
}
