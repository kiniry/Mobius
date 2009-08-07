package freeboogie.vcgen;

import java.util.ArrayList;

import genericutils.Closure;

import freeboogie.ast.Block;
import freeboogie.backend.Term;
import freeboogie.tc.TcInterface;

/**
 * Computes strongest postcondition for one {@code
 * Implementation}.
 *
 * This class receives a flow graph of blocks ({@code
 * SimpleGraph&lt;Block&gt;}, where each block must contain only
 * {@code AssertAssumeCmd}s) and computes preconditions and
 * postconditions for all nodes, verification conditions for
 * individual assertions, and a verification condition for all
 * assertion. (The implementation is inspired by strongest
 * postcondition calculus.)
 *
 * The graph must be acyclic.
 *
 * (The input can be obtained as follows: (a) parse BPL, (b) add
 * procedure specs to the body as assumes and assert, (c) build a
 * flow graph, (d) make that reducible, (e) eliminate loops, and
 * (f) passivate.)
 *
 * The formulas are built using a {@code TermBuilder} that is
 * handed to us by the user. That {@code TermBuilder} must know
 * about the terms "literal_pred", "and", "or", and "implies".
 *
 * The nodes with no predecessors are considered
 * initial; the nodes with no successors are considered
 * final. (So unreachable code blocks must be removed in
 * a previous phase.)
 *
 * TODO Give some guides in a document somewhere how to name terms.
 *
 * Each command is attached a precondition and a postcondition
 * according to the following definitions:
 * <pre>
 * pre(n) = TRUE                      if n is an entry point
 * pre(n) = OR_{m BEFORE n} post(m)   otherwise
 * post(n) = pre(n) AND term(expr(n)) if n is an assume
 * post(n) = pre(n)                   if n is an assert
 * </pre>
 *
 * The user can say (by calling {@code assertsAsAssumes}) that
 * asserts should be treated as they are also assumes (followed
 * by...)
 *
 * The verification condition is then computed as:
 * <pre>
 * VC = AND_{n is assert} (pre(n) IMPLIES term(expr(n)))
 * </pre>
 *
 * @param <T> the type of terms
 *
 * @author rgrig
 */
public class StrongestPostcondition<T extends Term<T>> extends ACalculus<T> {
  /**
   * Returns the precondition of {@code b}, which must be in
   * the last set flow graph.
   */
  private T pre(Block b) {
    T r = preCache.get(b);
    if (r != null) return r;
    ArrayList<T> toOr = new ArrayList<T>();
    for (Block p : flow.from(b)) 
      toOr.add(post(p));
    if (toOr.isEmpty())
      r = trueTerm;
    else
      r = term.mk("or", toOr);
    preCache.put(b, r);
    return r;
  }

  private T post(Block b) {
    T r = postCache.get(b);
    if (r != null) return r;
    r = pre(b);
    if (assumeAsserts || isAssume(b))
      r = term.mk("and", r, term(b));
    postCache.put(b, r);
    return r;
  }

  /**
   * Returns the verification condition for a particular command.
   * If {@code cmd} is an assume then I return TRUE.
   */
  protected T vc(Block b) {
    if (!isAssert(b)) return trueTerm;
    return term.mk("implies", pre(b), term(b));
  }

  @Override
  public T vc() {
    final ArrayList<T> vcs = new ArrayList<T>();
    flow.iterNode(new Closure<Block>() {
      @Override
      public void go(Block b) {
        vcs.add(vc(b));
      }
    });
    return term.mk("and", vcs);
  }
}
