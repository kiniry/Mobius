// $Id$

/**
 * The model class for non-empty Sequences.
 *
 * All of our model classes have referential equality, are pure,
 * functional, and executable.  All have been extensively tested with
 * JML/Junit and have been ESCed with ESC/Java2.0a8.
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
    @                             : getCachedAndOrMake((Pair)elts.second()));
    @*/

  //------------------------------------------------------------------------------
  // Queries

  /*@ also
    @ public normal_behavior
    @   requires !isEmpty();
    @   ensures  \result == head;
    @*/
  public /*@ pure @*/ Object head() {
    return elts.first();
  }

  /*@ also
    @ public normal_behavior
    @   requires !isEmpty();
    @   modifies \nothing;
    @   ensures  \result == tail;
    @ also
    @ private normal_behavior
    @   requires !isEmpty();
    @   modifies chain;
    @   ensures  \result == (elts.second() == null
    @                       ? EmptySequence.make()
    @                       : getCached(chain, (Pair)elts.second()));
    @*/
  public /*@ non_null @*/ /* observationally_pure */ Sequence tail() {
    return getCachedAndOrMake((Pair)elts.second());
  }

  //------------------------------------------------------------------------------
  // Selectors

  //------------------------------------------------------------------------------
  // Constructors and factory methods

  /*@ normal_behavior
    @   requires Pair.isChain(e);
    @   modifies elts;
    @   ensures  !isEmpty();
    @ also
    @ protected normal_behavior
    @   requires Pair.isChain(e);
    @   modifies elts;
    @   ensures  elts == e;
    @*/
  protected NonEmptySequence(/*@ non_null @*/ Pair e) {
    this.elts = e;
  }
}
