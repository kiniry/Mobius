public final class Pair
{
  /*@ public static invariant
    @   (\forall Pair p, q;; p == q <==> p.first() == q.first() && p.second() == q.second());
    @*/

  /*@ private normal_behavior
    @  ensures \result == (p == null ||
    @                      (p.first instanceof Pair &&
    @                      (p.second == null) || ((p.second instanceof Pair) &&
    @                                              elts_invariant((Pair)(p.second)))));
    @
    @ private pure static model boolean elts_invariant(Pair p);
    @*/

  //@ private static invariant elts_invariant(elts);
  private static /* null */ Pair elts = null;

  private final /* null */ Object first;
  private final /* null */ Object second;

  /*@ private normal_behavior
    @  modifies this.first, this.second;
    @  ensures this.first == first;
    @  ensures this.second == second;
    @*/
  private Pair(final Object first, final Object second) {
    this.first = first;
    this.second = second;
  }

  /*@ public normal_behavior
    @   modifies \nothing;
    @   ensures \result.first() == first;
    @   ensures \result.second() == second;
    @ also
    @ private normal_behavior
    @   modifies elts;
    @*/
  public static /*@ non_null @*/ Pair make(Object first, Object second) {
    for (Pair p = elts; p != null; p = (Pair)(p.second)) {
      if (p.first == first && p.second == second)
        return p;
      Pair q = (Pair)(p.first); //@ nowarn Cast;
      if (q.first == first && q.second == second)
        return q;
    }
    Pair result = new Pair(first, second);
    elts = new Pair(result, elts);
    return result;
  }

  /*@ normal_behavior
    @   modifies \nothing;
    @*/
  public /*@ pure @*/ Object first() {
    return first;
  }

  /*@ normal_behavior
    @   modifies \nothing;
    @*/
  public /*@ pure @*/ Object second() {
    return second;
  }
  
  /*@ also 
    @ normal_behavior
    @   modifies \nothing;
    @   ensures \result == (this == other);
    @*/
  public /*@ pure @*/ boolean equals(Object other) {
    return this == other;
  }
}
