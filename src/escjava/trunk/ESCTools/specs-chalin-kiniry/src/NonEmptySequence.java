// $Id$

/**
 * The (referential equality, functional, executable, pure) model
 * class for Sequences.
 *
 * @author Patrice Chalin
 * @author Joe Kiniry
 */

public final class NonEmptySequence extends Sequence
{
  //@ private invariant elts != null;

  /*@ public model Object head;
    @	in objectState;
    @ private represents head <- elts.first();
    @*/

  /*@ public model non_null Sequence tail;
    @	in objectState;
    @ private represents tail <- (elts.second() == null
    @                             ? EmptySequence.make()
    @                             : getCachedAndOrMake((Cons)elts.second()));
    @*/

  //------------------------------------------------------------------------------
  // Queries

  /*@ also
    @ public normal_behavior
    @  requires !isEmpty();
    @  ensures  \result == head;
    @*/
  public /*@ pure @*/ Object head() {
    return elts.first();
  }

  /*@ also
    @ public normal_behavior
    @  requires !isEmpty();
    @  modifies \nothing;
    @  ensures  \result == tail;
    @ also
    @ private normal_behavior
    @  requires !isEmpty();
    @  modifies chain;
    @  ensures \result == (elts.second() == null
    @                     ? EmptySequence.make()
    @                     : getCached(chain, (Cons)elts.second()));
    @*/
  public /*@ non_null @*/ /* observationally_pure */ Sequence tail() {
    return getCachedAndOrMake((Cons)elts.second());
  }

  //------------------------------------------------------------------------------
  // Selectors

  //------------------------------------------------------------------------------
  // Constructors and factory methods

  /*@ normal_behavior
    @   requires Cons.isChain(elts);
    @   modifies elts;
    @*/
  NonEmptySequence(/*@ non_null @*/ Cons e) {
    this.elts = e;
  }
}
