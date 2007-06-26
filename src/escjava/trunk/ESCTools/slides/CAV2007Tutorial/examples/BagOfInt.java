//@ refine "BagOfInt.jml";
class BagOfInt {

  private /*@ spec_public @*/ int[] a;
  private /*@ spec_public @*/ int n;

  public BagOfInt(int[] input) {
    n = input.length;
    a = new int[n];
    System.arraycopy(input, 0, a, 0, n);
  }

  public /*@ pure @*/ int occurrences(int i) {
    int count = 0;
    for (int j = 0; j < n; j++) {
      if (a[j] == i) {
        count++;
      }
    }
    return count;
  }

  public int extractMin() {
    int m = Integer.MAX_VALUE;
    int mindex = 0;
    for (int i = 1; i <= n; i++) {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    return m;
  }
}
