package test;

/**
 * Another example for tests.
 * Should not be changed (tests may stop working).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class Empty2 {

  private static int l = 0;

  private static int fib(final int n) {
    l++;
    if (n  <  2) {
      return n;
    }
    final int[] last = new int[3];
    last[0] = 0;
    last[1] = 1;
    for (int i = 2; i  <= n; i++) {
      last[i % 3] = last[(i - 1) % 3] + last[(i - 2) % 3];
    }
    return last[n % 3];
  }

  public static void main(final String[] args) {
    final int x = fib(1);
    final int y = fib(6);
    final int z = fib(Empty.c);
    final int d = x + y + z;
    System.out.println("n=" + d + ", l=" + l);
  }

  @SuppressWarnings("unused")
  private final String text = "aaa";

}
