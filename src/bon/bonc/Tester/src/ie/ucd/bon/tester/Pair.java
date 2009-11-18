package ie.ucd.bon.tester;

public class Pair <A,B> {

  private final A first;
  private final B second;

  public static <A, B> Pair<A, B> mk(A a, B b) {
    return new Pair<A, B>(a, b);
  }
  
  public Pair(A first, B second) {
    this.first = first;
    this.second = second;
  }

  public A getFirst() {
    return first;
  }

  public B getSecond() {
    return second;
  }
  
}
