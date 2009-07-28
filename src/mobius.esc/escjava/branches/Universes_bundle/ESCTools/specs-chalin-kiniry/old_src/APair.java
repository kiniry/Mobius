public final class APair implements Pair {
  public static final Pair empty = new APair();

  private Object first = null, second = null;

  private APair() {
  }

  public Pair make(final Object first, final Object second) {
    APair result = new APair();
    result.first = first;
    result.second = second;
    return result;
  }
  
  public Object first() {
    return first;
  }

  public Object second() {
    return second;
  }

  public Pair empty() {
    return empty;
  }

  public boolean equals(Object other) {
    return this == other;
  }
}