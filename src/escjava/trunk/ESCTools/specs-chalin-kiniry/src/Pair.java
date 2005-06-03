// $Id$

/**
 * Model class for immutable pairs.
 */

public final /*@ pure @*/ class Pair
{
  /*@ private static invariant
    @   (\forall Pair p;; Cons.isMember(chain, p));
    @*/

  /*@ public static invariant
    @   (\forall Pair p, q;; p == q <==> p.first() == q.first() && 
    @                                    p.second() == q.second());
    @*/

  //@ private static invariant Cons.isChain(chain);
  //@ private static invariant (* every first is a non-null Pair *);
  private static /* null */ Cons chain = null;

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
    @   modifies chain;
    @   ensures_redundantly Cons.isMember(chain, \result);
    @*/
  public static /*@ non_null @*/ Pair make(Object first, Object second) {
    for (Cons c = chain; c != null; c = (Cons)(c.second())) {
      Pair p = (Pair)(c.first());
      if (p.first == first && p.second == second)
        return p;
    }
    Pair result = new Pair(first, second);
    chain = new Cons(result, chain);
    return result;
  }

  /*@ normal_behavior
    @   modifies \nothing;
    @*/
  public Object first() {
    return first;
  }

  /*@ normal_behavior
    @   modifies \nothing;
    @*/
  public Object second() {
    return second;
  }
  
  /*@ also 
    @ normal_behavior
    @   modifies \nothing;
    @   ensures \result == (this == other);
    @*/
  public boolean equals(Object other) {
    return this == other;
  }
}