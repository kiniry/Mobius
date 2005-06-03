// $Id$

/**
 * The (referential equality, functional, executable, pure) model
 * class for Sequences.
 *
 * @author Patrice Chalin
 * @author Joe Kiniry
 */

public final /*@ pure @*/ class Sequence
{
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
   * The chain of all Sequences.
   */
  /*@ private static invariant
    @   (* chain contains all Sequences and only Sequences, that is ... *);
    @ private static invariant
    @   (\forall Object o;; Cons.isMember(chain, o) <==> (o instanceof Sequence));
    @ private static invariant Cons.isChain(chain);
    @ private static invariant (* every first is a non-null Sequence *);
    @*/
  private static /* null */ Cons chain = null;

  /**
   * The elements in this Sequence.
   */
  private /* null */ Cons elts = null;

  /*@ public model Object head;
    @              in objectState;
    @*/

  /*@ public model Sequence tail;
    @              in objectState;
    @*/
    
  /*@ public model \bigint length;
    @              in objectState;
    @ private represents length <- elts.length();
    @*/

  //@ public  invariant 0 <= length;
  //@ public  invariant_redundantly isEmpty() <==> 0 == length;
  //@ private invariant_redundantly elts == null <==> 0 == length;

  // TBC
  //@ private invariant (* Each Sequence object is uniquely determined by its elts.*);

  //------------------------------------------------------------------------------
  // Queries

  /*@ public normal_behavior
    @   ensures \result <==> elts == null;
    @*/
  public boolean isEmpty() {
    return (elts == null);
  }

  /*@ public normal_behavior
    @   ensures \result == length;
    @ public pure model \bigint length() {
    @   return elts.length();
    @ }
    @*/

  //  True iff 'o' is in this list.
  //  public pure boolean has(Object o);

  //------------------------------------------------------------------------------
  // Selectors

  /*@ public normal_behavior
    @  requires !isEmpty();
    @*/
  public Object head() {
    return elts.first();
  }

  /*@ public normal_behavior
    @  requires !isEmpty();
    @*/
  public /*@ non_null @*/ Sequence tail() {
    Cons someElts = (Cons)(elts.second());
    Sequence result = getCachedAndOrMake(someElts);
    return result;
  }

  //  Returns the item at index 'i'.
  //@ public pure model Object itemAt(\bigint i);

  //  Returns the last item in this sequence.
  //@ public pure model Object last();

  //------------------------------------------------------------------------------
  // Constructors and factory methods

  private Sequence(Cons elts) {
    this.elts = elts;
  }

  /*@ public normal_behavior
    @   ensures \result.isEmpty();
    @*/
  public static /*@ pure non_null @*/ Sequence empty() {
    return getCachedAndOrMake(null);
  }

  /*@ public normal_behavior
    @   ensures !\result.isEmpty();
    @   ensures \result.head() == o;
    @   ensures \result.tail() == this;
    @*/
  public /*@ non_null @*/ Sequence append(Object o) {
    return getCachedAndOrMake(new Cons(o, elts));
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
    @  requires getCachedHelper(chain, elts) != null;
    @  modifies \nothing;
    @  ensures  \result == getCachedHelper(chain, elts);
    @ also
    @ private normal_behavior
    @  requires getCachedHelper(chain, elts) == null;
    @  modifies chain;
    @  ensures  \fresh(\result);
    @  ensures  \result.elts == elts;
    @*/
  private static /*@ non_null @*/ /* non_pure */ Sequence 
    getCachedAndOrMake(Cons elts) 
  {
    Sequence result = getCached(elts);
    if (result == null) {
      result = new Sequence(elts);
      chain = new Cons(result, chain);
    }
    return(result);
  }

  /*@ private normal_behavior
    @   ensures \result == (chain == null
    @		? null
    @		: ((Sequence)chain.first()).elts == elts
    @			? (Sequence)chain.first()
    @			: getCachedHelper((Cons)(chain.second()), elts));
    @*/
  private static /*@ pure @*/ /* null */ Sequence getCachedHelper(/* null */ Cons chain,
                                                                  /*@ non_null */ Cons elts) {
    if(chain == null)
      return null;

    Sequence k = (Sequence)chain.first();
    return k.elts == elts
      ? k
      : getCachedHelper((Cons)(chain.second()), elts);
  }

  /*@ private normal_behavior
    @  // requires (\exists Sequence p;; p.elts == elts);
    @  // ensures  (\exists Sequence p; p.elts == elts; \result == p);
    @  requires getCachedHelper(chain, elts) != null;
    @  ensures  \result == getCachedHelper(chain, elts);
    @ also
    @ private normal_behavior
    @  // requires !(\exists Sequence p;; p.elts == elts);
    @  requires getCachedHelper(chain, elts) == null;
    @  ensures  \result == null;
    @*/
  private static /*@ pure @*/ /* null */ Sequence getCached(/* null */ Cons elts) {
    // look for pre-existing chain of elements elts
    for (Cons p = chain; p != null; p = (Cons)(p.second())) {
      Sequence aSequence = (Sequence)(p.first());
      Cons q = aSequence.elts;
      if (elts == q)
        return aSequence;
    }
    return null;
  }
}
