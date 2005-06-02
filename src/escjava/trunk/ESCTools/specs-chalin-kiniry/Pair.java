// $Id$

public final class Pair
{
  /*@ private static invariant
    @   (\forall Pair p;; lookup(p));
    @*/

  /*@ public static invariant
    @   (\forall Pair p, q;; p == q <==> p.first() == q.first() && 
    @                                    p.second() == q.second());
    @*/

  /*@ private normal_behavior
    @  ensures \result == (p == null ||
    @                      (p.first instanceof Pair &&
    @                      (p.second == null) || ((p.second instanceof Pair) &&
    @                                              chain_invariant((Pair)(p.second)))));
    @ private pure static model boolean chain_invariant(Pair p) {
    @   return (p == null ||
    @           (p.first instanceof Pair &&
    @            (p.second == null) || ((p.second instanceof Pair) &&
    @                                    chain_invariant((Pair)(p.second)))));
    @ }
    @*/

  //@ private static invariant chain_invariant(chain);
  //@ private static invariant !cyclic(chain);

  private static /* null */ Pair chain = null;

  private final /* null */ Object first;
  private final /* null */ Object second;

  /**
   * Look for the node current starting from start and stopping at
   * stop.  If we find it, return true, otherwise, return false.
   */
  private static /*@ pure @*/ boolean inChain(/*@ non_null @*/ Pair start,
                                              /*@ non_null @*/ Pair stop, 
                                              /*@ non_null @*/ Pair current) {
    for (Pair p = start;
         p != null && p != stop;
         p = (Pair)p.second) {
      if (p == current)
        return true;
    }
    return false;
  }

  /**
   * @return true if the chain starting with p is cyclic.
   */
  private static /*@ pure @*/ boolean cyclic(Pair p) {
    if (p == null)
      return false;
    Pair start = p;
    Pair stop = p;
    // invariant: there are no duplicates in between start and stop.
    for (Pair current = (Pair)start.second(); 
         current != null; 
         stop = current, current = (Pair)current.second()) {
      if (inChain(start, stop, current))
        return true;
    }
    return false;
  }

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
    @   modifies chain;
    @   ensures_redundantly lookup(\result);
    @*/
  public static /*@ non_null @*/ Pair make(Object first, Object second) {
    for (Pair p = chain; p != null; p = (Pair)(p.second)) {
      if (p.first == first && p.second == second)
        return p;
      Pair q = (Pair)(p.first); //@ nowarn Cast;
      if (q.first == first && q.second == second)
        return q;
    }
    Pair result = new Pair(first, second);
    chain = new Pair(result, chain);
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

  // -----------------------------------------------------------------
  // Helpers

  /*@ private normal_behavior
    @   ensures \result == (c == null
    @                      ? null
    @                      : (c == p 
    @                        ? p 
    @                        : (Pair)c.first() == p 
    @                          ? p
    @                          : lookupHelper((Pair)c.second(), p)));
    @*/
  private /*@ pure @*/ static Pair lookupHelper(Pair c, /*@ non_null @*/ Pair p) {
    return (c == null
            ? null
            : (c == p 
               ? p 
               : (Pair)c.first() == p 
                 ? p
                 : lookupHelper((Pair)c.second(), p)));
  }

  /*@ private normal_behavior
    @   ensures \result == (lookupHelper(chain, p) != null);
    @*/
  private /*@ pure @*/ static boolean lookup(Pair p) {
    return (lookupHelper(chain, p) != null);
  }
}
