// $Id$

/**
 * The (referential equality, functional, executable, pure) model
 * class for empty Sequences.
 *
 * @author Patrice Chalin
 * @author Joe Kiniry
 */

public final class EmptySequence extends Sequence
{
  private static final EmptySequence theEmptySequence = new EmptySequence();

  static {
    cache(theEmptySequence);
  }

  //------------------------------------------------------------------------------
  // Queries

  //------------------------------------------------------------------------------
  // Selectors

  public Object head() throws RuntimeException {
    assert false;
    throw new RuntimeException();
  }

  public Sequence tail() throws RuntimeException {
    assert false;
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

  /*@ private normal_behavior
    @   modifies elts;
    @   ensures elts == null;
    @*/
  private EmptySequence() {
    this.elts = null;
   }
}
