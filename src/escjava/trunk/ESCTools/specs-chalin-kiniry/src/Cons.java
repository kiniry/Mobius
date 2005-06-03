// $Id$

/**
 * Cons objects can be "chained" together.  We formally define "chain"
 * as follows:
 * - null is a chain
 * - a Cons object is a chain if its second is a chain.
 * (nothing else is a chain).
 *
 * Note: it is impossible to create cyclic chains because Cons cells
 * are immutable and can only be constructed by the single constuctor
 * herein.
 */

// immutable!
public final class Cons
{
  /*@ spec_public @*/ private final /* null */ Object first;
  /*@ spec_public @*/ private final /* null */ Object second;

  /*@ private normal_behavior
    @  modifies this.first, this.second;
    @  ensures this.first == first;
    @  ensures this.second == second;
    @*/
  public Cons(final Object first, final Object second) {
    this.first = first;
    this.second = second;
  }

  /*@ normal_behavior
    @   modifies \nothing;
    @   ensures \result == first;
    @*/
  public /*@ pure @*/ Object first() {
    return first;
  }

  /*@ normal_behavior
    @   modifies \nothing;
    @   ensures \result == second;
    @*/
  public /*@ pure @*/ Object second() {
    return second;
  }
  
  /*@ also 
    @ public normal_behavior
    @   modifies \nothing;
    @   ensures \result == ((other instanceof Cons) &&
    @                       first() == ((Cons)other).first() &&
    @                       second() == ((Cons)other).second());
    @*/
  public /*@ pure @*/ boolean equals(Object other) {
    return (other instanceof Cons) &&
      first() == ((Cons)other).first() &&
      second() == ((Cons)other).second();
  }

  // -----------------------------------------------------------------
  // Helpers

  /*@ public normal_behavior
    @   requires isChain(chain);
    @   ensures \result == (chain != null && 
    @                       (chain.first() == o ||
    @                        isMemberHelper((Cons)chain.second(), o)));
    @*/
  /*@ spec_public @*/ private /*@ pure @*/ static boolean 
    isMemberHelper(Cons chain,
                   /*@ non_null @*/ Object o) {
    return (chain != null && 
            (chain.first == o || isMemberHelper((Cons)chain.second, o)));
  }

  /*@ public normal_behavior
    @   requires isChain(chain);
    @   ensures \result == isMemberHelper(chain, o);
    @*/
  public /*@ pure @*/ static boolean isMember(Cons chain,
                                              /*@ non_null @*/ Object o) {
    return isMemberHelper(chain, o);
  }

  /*@ public normal_behavior
    @   ensures \result == 
    @     (c == null || c.second == null || 
    @      (c.second instanceof Cons && isChain((Cons)c.second)));
    @*/
  public static /*@ pure @*/ boolean isChain(Cons c) {
    return c == null || c.second == null || 
      (c.second instanceof Cons && isChain((Cons)c.second));
  }
}
