// $Id$

/**
 * Model class for immutable pairs.
 *
 * @author Patrice Chalin
 * @author Joe Kiniry
 */

public final /*@ pure @*/ class Pair
{
  /*@ public static invariant
    @   (* two pairs are referentially equal iff their firsts/seconds are 
    @      referentially equal, that is ... *);
    @ public static invariant
    @   (\forall Pair p, q;; p == q <==> p.first() == q.first() && 
    @                                    p.second() == q.second());
    @*/

  /**
   * The chain of all Pairs.
   */
  /*@ private static invariant
    @   (* chain contains all Pairs and only Pairs, that is ... *);
    @ private static invariant
    @   (\forall Object o;; Cons.isMember(chain, o) <==> (o instanceof Pair));
    @ private static invariant Cons.isChain(chain);
    @ private static invariant (* every first is a non-null Pair *);
    @*/
  private static /* null */ Cons chain = null;

  /*@ spec_public @*/ private final /* null */ Object first;
  /*@ spec_public @*/ private final /* null */ Object second;

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
    @   requires (\exists Pair p;; p.first() == first && p.second() == second);
    @   requires_redundantly inChain(first, second);
    @   modifies \nothing;
    @   ensures_redundantly Cons.isMember(chain, \result);
    @ also
    @ private normal_behavior
    @   requires !(\exists Pair p;; p.first() == first && p.second() == second);
    @   requires_redundantly !inChain(first, second);
    @   modifies chain;
    @   ensures \fresh(\result);
    @   ensures chain.first() == \result && chain.second() == \old(chain);
    @   ensures_redundantly Cons.isMember(chain, \result);
    @*/
  public static /*@ non_null @*/ /* non_pure */ Pair make(Object first, Object second) {
    Pair result = getCached(first, second);
    if (result == null)
      result = new Pair(first, second);
    chain = new Cons(result, chain);
    return result;
  }

  /*@ public normal_behavior
    @   ensures \result == first;
    @*/
  public Object first() {
    return first;
  }

  /*@ public normal_behavior
    @   ensures \result == second;
    @*/
  public Object second() {
    return second;
  }
  
  /*@ also 
    @ normal_behavior
    @   ensures \result == (this == other);
    @*/
  public boolean equals(Object other) {
    return this == other;
  }

  //- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // Helpers

  /*@ private normal_behavior
    @   ensures \result == (p != null && 
    @			    p.first() == first && p.second() == second);
    @*/
  private static /*@ pure @*/ boolean same(/* null */ Pair p, 
                                           /* null */ Object first, 
                                           /* null */ Object second)
  {
    return p != null && p.first() == first && p.second() == second;
  }

  /*@ private normal_behavior
    @   ensures \result == (chain == null
    @	  ? null
    @	  : same((Pair)chain.first(), first, second)
    @		? (Pair)chain.first()
    @		: getCachedHelper((Cons)(chain.second()), first, second));
    @*/
  private static /*@ pure @*/ /* null */ 
    Pair getCachedHelper(/* null */ Cons chain,
                                /* null */ Object first, 
                                /* null */ Object second)
  {
    if(chain == null)
      return null;

    Pair p = (Pair)chain.first();
    return same(p, first, second)
      ? p
      : getCachedHelper((Cons)chain.second(), first, second);
  }

  /**
   * Checks to see if a Pair with 'first' and 'second' is already in our chain.
   */
  /*@ private normal_behavior
    @   ensures (* returns the Pair [first, second] in chain, otherwise returns null *);
    @   ensures \result == getCachedHelper(chain, first, second);
    @*/
  private static /*@ pure @*/ /* null */ Pair getCached(Object first, Object second) {
    for (Cons c = chain; c != null; c = (Cons)(c.second())) {
      Pair p = (Pair)(c.first());
      if (p.first == first && p.second == second)
        return p;
    }
    return null;
  }

  /*@ private normal_behavior
    @   ensures \result <==> getCached(first, second) != null;
    @*/
  private static /*@ pure @*/ boolean inChain(Object first, Object second) {
    return getCached(first, second) != null;
  }
}