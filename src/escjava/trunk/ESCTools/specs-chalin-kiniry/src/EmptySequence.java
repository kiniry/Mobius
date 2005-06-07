// $Id$

/**
 * The model class for empty Sequences.
 *
 * All of our model classes have referential equality, are pure,
 * functional, and executable.  All have been extensively tested with
 * JML/Junit and have been ESCed with ESC/Java2.0a8.
 *
 * @author Patrice Chalin
 * @author Joe Kiniry
 */

public final class EmptySequence extends Sequence
{
  //@ private invariant elts == null;
  
  private static final EmptySequence theEmptySequence = new EmptySequence();

  static {
    cache(theEmptySequence);
  }

  //------------------------------------------------------------------------------
  // Queries

  //------------------------------------------------------------------------------
  // Selectors

  public Object head() throws RuntimeException {
    throw new RuntimeException();
  }

  public Sequence tail() throws RuntimeException {
    throw new RuntimeException();
  }

  //------------------------------------------------------------------------------
  // Constructors and factory methods

  /*@ public normal_behavior
    @   ensures \result.isEmpty();
    @*/
  public static /*@ pure non_null @*/ Sequence make() {
    return theEmptySequence;
  }

  /*@ public normal_behavior
    @   ensures isEmpty();
    @ protected normal_behavior
    @   ensures elts == null;
    @*/
  private /*@ pure @*/ EmptySequence() {
    // relying upon default initialization of elts
    //@ assert elts == null;
  }
}
