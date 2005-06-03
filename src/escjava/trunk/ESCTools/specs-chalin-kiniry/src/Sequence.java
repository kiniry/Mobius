// $Id$

/**
 * The (referential equality, functional, executable, pure) model class for lists.
 *
 * @author Patrice Chalin
 * @author Joe Kiniry
 */

public final /*@ pure @*/ class Sequence
{
  /**
   * The (global) chain of Sequences.  Every Sequence object is in our chain.
   */
  private static /* null */ Pair chain = null;

  /*@ private static invariant
    @   (\forall Sequence k;; Sequence.lookup(k));
    @*/

  /*
   * This invariant ensures that there is at most one Sequence with a
   * given head and tail.
   */
  /*@ public static invariant
    @   (\forall Sequence p, q;; p == q <==> 
    @           p.isEmpty() && q.isEmpty() ||
    @		(!p.isEmpty() && !q.isEmpty() && 
    @            p.head() == q.head() && 
    @		 p.tail() == q.tail())
    @	);
    @*/

  /**
   * The elements in this Sequence.
   */
  /*@ spec_public @*/ private /* null */ Pair elts = null;
  //@ public model \bigint _length;
  //@   in objectState;
  //@ private represents _length <- length(elts);
  //@ public invariant 0 <= _length;
  //@ public invariant isEmpty() <==> 0 == _length;
  //@ private invariant_redundantly elts == null <==> 0 == _length;

  //------------------------------------------------------------------------------
  // Queries

  /*@ public normal_behavior
    @   ensures \result <==> elts == null;
    @*/
  public boolean isEmpty() {
    return (elts == null);
  }

  //  The number of times a given element 'o' occurs in the sequence.
  //@ public pure model \bigint length(Object o);

  //  True iff 'o' is in this list.
  //  public pure boolean has(Object o);

  //------------------------------------------------------------------------------
  // Selectors

  /*@ public normal_behavior
    @  requires !isEmpty();
    @  modifies \nothing;
    @  ensures \result == elts.first();
    @*/
  public Object head() {
    return elts.first();
  }

  /*@ public normal_behavior
    @  requires !isEmpty();
    @  modifies \nothing;
    @  ensures \result.elts == elts.second();
    @*/
  public Sequence tail() {
    Pair someElts = (Pair)(elts.second());
    Sequence result = lookupAndOrMake(someElts);
    return result;
  }

  //  Returns the item at index 'i'.
  //@ public pure model Object itemAt(\bigint i);

  //  Returns the last item in this sequence.
  //@ public pure model Object last();

  //------------------------------------------------------------------------------
  // Constructors and factory methods

  private Sequence(Pair elts) {
    this.elts = elts;
  }

  /*@ public normal_behavior
    @   modifies \nothing;
    @   ensures \result.isEmpty();
    @*/
  public static /*@ non_null @*/ Sequence empty() {
    return lookupAndOrMake(null);
  }

  /*@ ensures \result == (p == null
    @   ? 0 
    @   : (p.second() instanceof Pair) ? 1 + length((Pair)(p.second())) : 1);
    @
    @ private static pure model \bigint length(Pair p) {
    @   return (p == null
    @    ? 0 
    @    : (p.second() instanceof Pair) ? 1 + length((Pair)(p.second())) : 1);
    @ }    
    @*/

  /*@ public normal_behavior
    @   ensures \result == _length;
    @ public pure model \bigint length() {
    @   return length(elts);
    @ }
    @*/

  /*@ public normal_behavior
    @   ensures !\result.isEmpty();
    @   ensures \result.head() == o;
    @   ensures \result.tail() == this;
    @*/
  public /*@ non_null @*/ Sequence append(Object o) {
    return lookupAndOrMake(Pair.make(o, elts));
  }

  /*@ also
    @ public normal_behavior
    @   ensures \result == (this == o);
    @*/
  public boolean equals(Object o) {
    return this == o;
  }

  //- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  // Helpers methods

  /*@ private normal_behavior
    @   ensures \result == (chain == null
    @		? null
    @		: ((Sequence)chain.first()).elts == elts
    @			? (Sequence)chain.first()
    @			: lookupHelper((Pair)(chain.second()), elts));
    @*/
  private static /* null */ Sequence lookupHelper(/* null */ Pair chain, /*@ non_null */ Pair elts) {
    if(chain == null)
      return null;

    Sequence k = (Sequence)chain.first();
    return k.elts == elts
      ? k
      : lookupHelper((Pair)(chain.second()), elts);
  }

  /*@ private normal_behavior
    @  // requires (\exists Sequence p;; p.elts == elts);
    @  // ensures  (\exists Sequence p; p.elts == elts; \result == p);
    @  requires lookupHelper(chain, elts) != null;
    @  ensures  \result == lookupHelper(chain, elts);
    @ also
    @ private normal_behavior
    @  // requires !(\exists Sequence p;; p.elts == elts);
    @  requires lookupHelper(chain, elts) == null;
    @  ensures  \result == null;
    @*/
  private static /* null */ Sequence lookup(/* null */ Pair elts) {
    // look for pre-existing chain of elements elts
    for (Pair p = chain; p != null; p = (Pair)(p.second())) {
      Sequence aSequence = (Sequence)(p.first());
      Pair q = aSequence.elts;
      if (elts == q)
        return aSequence;
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
  private static /*@ non_null @*/ Sequence lookupAndOrMake(Pair elts) {
    Sequence result = lookup(elts);
    if (result == null) {
      result = new Sequence(elts);
      chain = Pair.make(result, chain);
    }
    return(result);
  }

  /*@ private normal_behavior
    @   ensures \result <==>
    @       (p != null && (p.first() == k || lookupHelper((Pair)(p.second()), k)));
    @   ensures \result <==> lookupHelper((Pair)(p.second()), k.elts) != null;
    @*/
  private static boolean lookupHelper(/* null */ Pair p, /*@ non_null */ Sequence k) {
    return p != null && (p.first() == k || lookupHelper((Pair)(p.second()), k));
  }

  /*@ private normal_behavior
    @  ensures \result <==> lookupHelper(chain, k);
    @*/
  private static boolean lookup(/*@ non_null @*/ Sequence k) {
    for (Pair p = chain; p != null; p = (Pair)(p.second())) {
      if (p.first() == k)
        return true;
    }
    return false;
  }
}
