class FinalPair
{
  private static final /*@ non_null @*/ FinalPair nullPair = new FinalPair(null, null);
  /*@ private normal_behavior
    @  ensures \result == (cpair == null ||
    @                      (cpair.first instanceof FinalPair &&
    @                      (cpair.second == null) || ((cpair.second instanceof FinalPair) &&
    @                                                 elts_invariant((FinalPair)(cpair.second)))));
    @
    @ private pure model boolean elts_invariant(FinalPair cpair) {
    @       return (cpair == null ||
    @                      (cpair.first instanceof FinalPair &&
    @                      (cpair.second == null) || ((cpair.second instanceof FinalPair) &&
    @                                                 elts_invariant((FinalPair)(cpair.second)))));
    @ }
    @*/

  //@ private invariant elts_invariant(elts);
  private static /* null */ FinalPair elts = null;

  private final /* null */ Object first;
  private final /* null */ Object second;

  /*@ private normal_behavior
    @  modifies this.first, this.second;
    @  ensures this.first == first 
    @       && this.second == second;
    @*/
  private FinalPair(final Object first, final Object second) {
    this.first = first;
    this.second = second;
  }

  /*@ normal_behavior
    @   modifies \nothing;
    @   ensures \result.first() == null 
    @        && \result.second() == null;
    @*/
  /*@ non_null @*/ FinalPair nullPair() {
    return nullPair;
  }

  /*@ normal_behavior
    @   modifies this.objectState;
    @   ensures \result.first() == first;
    @   ensures \result.second() == second;
    @*/
  /*@ non_null @*/ FinalPair make(Object first, Object second) {
    if (first == null && second == null)
      return nullPair;
    if (elts != null)
      for (FinalPair p = elts; p != null ; p = (FinalPair)(p.second)) {
        FinalPair q = (FinalPair)(p.first);
        if (q.first == first && q.second == second)
          return q;
      }
    FinalPair result = new FinalPair(first, second);
    elts = new FinalPair(result, elts);
    return result;
  }

  /*@ normal_behavior
    @   modifies \nothing;
    @*/
  /*@ pure @*/ Object first() {
    return first;
  }

  /*@ normal_behavior
    @   modifies \nothing;
    @*/
  /*@ pure @*/ Object second() {
    return second;
  }
  
  /*@ also 
    @ normal_behavior
    @   ensures \result == (this == other);
    @   ensures \result == (\typeof(other) == \type(Pair) && ((Pair)other).first() == first() && ((Pair)other).second() == second());
    @*/
  /*@ pure @*/ boolean equals(Object other) {
    return this == other;
  }
}
