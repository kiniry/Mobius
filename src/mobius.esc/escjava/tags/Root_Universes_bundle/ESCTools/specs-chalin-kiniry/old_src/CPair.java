public final class CPair implements Pair 
{
  private static final /*@ non_null @*/ Pair nullPair = new CPair(null, null);
  /*@ private normal_behavior
    @  ensures \result == (cpair == null ||
    @                      (cpair.first instanceof Pair &&
    @                      (cpair.second == null) || ((cpair.second instanceof CPair) &&
    @                                                 elts_invariant((CPair)(cpair.second)))));
    @
    @ private pure model boolean elts_invariant(CPair cpair) {
    @       return (cpair == null ||
    @                      (cpair.first instanceof Pair &&
    @                      (cpair.second == null) || ((cpair.second instanceof CPair) &&
    @                                                 elts_invariant((CPair)(cpair.second)))));
    @ }
    @*/

  //@ private invariant elts_invariant(elts);
  private static /* null */ CPair elts = null;

  private final /* null */ Object first;
  private final /* null */ Object second;

  /*@ private normal_behavior
    @  modifies this.first, this.second;
    @  ensures this.first == first 
    @       && this.second == second;
    @*/
  private CPair(final Object first, final Object second) {
    this.first = first;
    this.second = second;
  }

  public /*@ non_null @*/ Pair nullPair() {
    return nullPair;
  }

  public /*@ non_null @*/ Pair make(final Object first, final Object second) {
    if (first == null && second == null)
      return nullPair;
    if (elts != null)
      for (CPair p = elts; p != null ; p = (CPair)(p.second)) {
        CPair q = (CPair)(p.first);
        if (q.first == first && q.second == second)
          return q;
      }
    CPair result = new CPair(first, second);
    elts = new CPair(result, elts);
    return result;
  }
  
  public Object first() {
    return first;
  }

  public Object second() {
    return second;
  }

  public boolean equals(Object other) {
    return this == other;
  }
}