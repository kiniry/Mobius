package astgen;

import java.util.HashSet;

import genericutils.SimpleGraph;


/**
  Helps building a transitive relation such as <i>subtype</i> or
  <i>convertible</i>.

  The user informs this class when aRb and when <i>not</i> aRb.
  He can then ask if xRy and the answer, YES/NO/UNKNOWN, will
  take into account transitivity.

  Other queries are: what is the set of y (a) such that xRy for
  a given x; or (b) such that yRx for a given x; (c) what is a
  minimum transitive reduction of R? The last question should be
  asked only when R is complete (that is, it is known for all x,
  y if xRy).

  @param <N> the type of nodes
 */
public class TransitiveRelation<N> {
  private SimpleGraph<N> R = new SimpleGraph<N>();
  private SimpleGraph<N> notR = new SimpleGraph<N>();

  /** Record xRy. */
  public void mkR(N x, N y) {
    assert !notR(x, y);
    R.edge(x, y);
  }
 
  /** Record <i>not</i> xRy. */
  public void mkNotR(N x, N y) {
    assert !r(x, y);
    notR.edge(x, y);
  }

  /** xRy? */
  public boolean r(N x, N y) {
    assert false: "todo";
    return false;
  }

  /** not xRy ? */
  public boolean notR(N x, N y) {
    assert false: "todo";
    return false;
  }

  /** Returns all y such that xRy. */
  public HashSet<N> after(N x) {
    assert false: "todo";
    return null;
  }

  /** Returns all x such that xRy. */
  public HashSet<N> before(N y) {
    assert false: "todo";
    return null;
  }

  /** Computes the minimum transitive reduction of R. */
  public SimpleGraph<N> transitiveReduction() {
    assert false: "todo";
    return null;
  }
}


