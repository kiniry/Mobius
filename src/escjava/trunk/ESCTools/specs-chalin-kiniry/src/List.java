// $Id$

/**
 * The (referential equality, functional, executable, pure) model class for lists.
 *
 * @author Patrice Chalin
 * @author Joe Kiniry
 */

public final class List
{
  /**
   * The (global) chain of Lists.  Every List object is in our chain.
   */
  private static /* null */ Pair chain = null;

  /*@ private static invariant
    @   (\forall List k;; List.lookup(k));
    @*/

  /*
   * This invariant ensures that there is at most one List with a
   * given head and tail.
   */
  /*@ public static invariant
    @   (\forall List p, q;; p == q <==> 
    @           p.isEmpty() && q.isEmpty() ||
    @		(!p.isEmpty() && !q.isEmpty() && 
    @            p.head() == q.head() && 
    @		 p.tail() == q.tail())
    @	);
    @*/

  /**
   * The elements in this List.
   */
  /*@ spec_public @*/ private /* null */ Pair elts = null;
  //@ public model \bigint _size;
  //@ private represents _size <- count(elts);

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

  /*@ ensures \result == (p == null
    @   ? 0 
    @   : (p.second() instanceof Pair) ? 1 + count((Pair)(p.second())) : 1);
    @
    @ private static pure model \bigint count(Pair p) {
    @   return (p == null
    @    ? 0 
    @    : (p.second() instanceof Pair) ? 1 + count((Pair)(p.second())) : 1);
    @ }    
    @*/

  /*@ public normal_behavior
    @   ensures \result == _size;
    @ public pure model \bigint size() {
    @   return count(elts);
    @ }
    @*/

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
    @   ensures \result == (chain == null
    @		? null
    @		: ((List)chain.first()).elts == elts
    @			? (List)chain.first()
    @			: lookupHelper((Pair)(chain.second()), elts));
    @*/
  private static /*@ pure @*//*null*/ List lookupHelper(/* null */ Pair chain, /*@ non_null */ Pair elts) {
    if(chain == null)
      return null;

    List k = (List)chain.first();
    return k.elts == elts
      ? k
      : lookupHelper((Pair)(chain.second()), elts);
  }

  /*@ private normal_behavior
    @  // requires (\exists List p;; p.elts == elts);
    @  // ensures  (\exists List p; p.elts == elts; \result == p);
    @  requires lookupHelper(chain, elts) != null;
    @  ensures  \result == lookupHelper(chain, elts);
    @ also
    @ private normal_behavior
    @  // requires !(\exists List p;; p.elts == elts);
    @  requires lookupHelper(chain, elts) == null;
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

  /*@ private normal_behavior
    @  requires lookupHelper(chain, elts) != null;
    @  modifies \nothing;
    @  ensures  \result == lookupHelper(chain, elts);
    @ also
    @ private normal_behavior
    @  requires lookupHelper(chain, elts) == null;
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
    @       (p != null && (p.first() == k || lookupHelper((Pair)(p.second()), k)));
    @   ensures \result <==> lookupHelper((Pair)(p.second()), k.elts) != null;
    @*/
  private static /*@ pure @*/ boolean lookupHelper(/* null */ Pair p, /*@ non_null */ List k) {
    return p != null && (p.first() == k || lookupHelper((Pair)(p.second()), k));
  }

  /*@ private normal_behavior
    @  ensures \result <==> lookupHelper(chain, k);
    @*/
  private /*@pure*/ static boolean lookup(/*@non_null*/ List k) {
    for (Pair p = chain; p != null; p = (Pair)(p.second())) {
      if (p.first() == k)
        return true;
    }
    return false;
  }
}
