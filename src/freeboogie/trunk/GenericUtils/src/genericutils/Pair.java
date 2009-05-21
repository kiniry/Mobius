package genericutils;

/**
 * A pair.
 *
 * @author rgrig 
 * @param <F> the type of the first element
 * @param <S> the type of the second element
 */
public final class Pair<F, S> {
  private Pair(F f, S s) { first = f; second = s; }
  public static <F, S> Pair<F, S> of(F f, S s) { return new Pair<F, S>(f, s); }

  public F first;
  public S second;

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof Pair)) return false;
    Pair p = (Pair)o;
    boolean fok = first == null? p.first == null : first.equals(p.first);
    boolean sok = second == null? p.second == null : second.equals(p.second);
    return fok && sok;
  }

  @Override
  public int hashCode() {
    int ha = first == null? 0 : first.hashCode();
    int hb = second == null? 0 : second.hashCode();
    return ha + hb;
  }
}
