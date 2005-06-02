// $Id$

public final class List
{
  /*@ public static invariant
    @  (\forall List k; (* k is in the chain lists *));
    @  // (\forall Object o; (* o is in the chain lists *) <==> o instanceof List);
    @*/

  /*@ public static invariant
    @   (\forall List p, q;; p == q <==> 
    @           p.isEmpty() && q.isEmpty() ||
    @		(!p.isEmpty() && !q.isEmpty() && 
    @            p.head() == q.head() && 
    @		 p.tail() == q.tail())
    @	);
    @*/
  private static /* null */ Pair chain = null;

  /*@ spec_public @*/ private /* null */ Pair elts;

  //------------------------------------------------------------------------------
  // Queries

  /*@ public normal_behavior
    @   ensures \result <==> elts == null;
    @*/
  public /*@ pure @*/ boolean isEmpty() {
    return (elts == null);
  }

  //------------------------------------------------------------------------------
  // Selectors

  /*@ public normal_behavior
    @  requires !isEmpty();
    @  modifies \nothing;
    @  ensures \result == elts.first();
    @*/
  public /*@ pure @*/ Object head() {
    return elts.first();
  }

  /*@ public normal_behavior
    @  requires !isEmpty();
    @  modifies \nothing;
    @  ensures \result.elts == elts.second();
    @*/
  public /*@ pure @*/ List tail() {
    Pair someElts = (Pair)(elts.second());
    List result = lookupAndOrMake(someElts);
    return result;
  }

  //------------------------------------------------------------------------------
  // Constructors and factory methods

  private List(Pair elts) {
    this.elts = elts;
  }

  /*@ public normal_behavior
    @   modifies \nothing;
    @   ensures \result.isEmpty();
    @*/
  public static /*@ pure non_null @*/ List empty() {
    return lookupAndOrMake(null);
  }

  /*@ public normal_behavior
    @   ensures !\result.isEmpty();
    @   ensures \result.head() == o;
    @   ensures \result.tail() == this;
    @*/
  public /*@ pure non_null @*/ List append(Object o) {
    return lookupAndOrMake(Pair.make(o, elts));
  }

  //- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // Helpers methods

  /*@ private normal_behavior
    @  requires (\exists List p;; p.elts == elts);
    @  modifies \nothing;
    @  ensures  (\exists List p; p.elts == elts; \result == p);
    @ also
    @ private normal_behavior
    @  requires !(\exists List p;; p.elts == elts);
    @  modifies chain;
    @  ensures  \fresh(\result);
    @  ensures  \result.elts == elts;
    @*/
  private static /*@ non_null @*/ List lookupAndOrMake(Pair elts) {
    List result = lookup(elts);
    if (result == null) {
      result = new List(elts);
      chain = Pair.make(result, chain);
    }
    return(result);
  }

  /*@ private normal_behavior
    @   ensures \result <==> 
    @       (p != null && p.first() == k || lookupHelper((Pair)(p.second()), k));
    @*/
  private static /*@ pure @*/ boolean lookupHelper(/* null */ Pair p, /*@ non_null */ List k) {
    return p != null && p.first() == k || lookupHelper((Pair)(p.second()), k);
  }

  /*@ private normal_behavior
    @  ensures \result <==> lookupHelper(chain, k);
    @*/
  private /*@pure*/ static boolean bLookup(/*@non_null*/ List k) {
    for (Pair p = chain; p != null; p = (Pair)(p.second())) {
      if (p.first() == k)
        return true;
    }
    return false;
  }

  /*@ private normal_behavior
    @  requires (\exists List p;; p.elts == elts);
    @  ensures  (\exists List p; p.elts == elts; \result == p);
    @ also
    @ private normal_behavior
    @  requires !(\exists List p;; p.elts == elts);
    @  ensures  \result == null;
    @*/
  private /*@pure*/ static /*null*/ List lookup(/*null*/ Pair elts) {
    // look for pre-existing chain of elements elts
    for (Pair p = chain; p != null; p = (Pair)(p.second())) {
      List aList = (List)(p.first());
      Pair q = aList.elts;
      if (elts == q)
        return aList;
    }
    return null;
  }
}
