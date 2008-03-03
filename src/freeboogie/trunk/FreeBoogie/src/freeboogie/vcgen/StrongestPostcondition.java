package freeboogie.vcgen;

import java.util.HashMap;
import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.backend.Prover;
import freeboogie.backend.Term;
import freeboogie.backend.TermBuilder;
import freeboogie.tc.*;

/**
 * Computes strongest postcondition for one {@code
 * Implementation}.
 *
 * This class receives a flow graph of commands ({@code
 * SimpleGraph<AssertAssumeCmd>}) and computes preconditions and
 * postconditions for all nodes, verification conditions for
 * individual assertions, and a verification condition for all
 * assertion.
 *
 * The graph must be acyclic.
 *
 * (The input can be obtained as follows: (a) parse BPL, (b) add
 * procedure specs to the body as assumes and assert, (c) build a
 * flow graph, (d) make that reducible, (e) eliminate loops, and
 * (f) passivate.)
 *
 * The formulas are built using a {@code TermBuilder} that
 * is handed to us by the user. That {@code TermBuilder}
 * must know about the terms "true", "and", "or", and "implies".
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
 * @author rgrig
 * @author reviewed by TODO
 */
public class StrongestPostcondition {

  // used mainly for debugging
  static private final Logger log = Logger.getLogger("freeboogie.vcgen");

  // builds terms for a specific theorem prover
  private TermBuilder term;
  
  // the preconditions of each command
  private HashMap<AssertAssumeCmd, Term> pre;

  // the postconditions of each command
  private HashMap<AssertAssumeCmd, Term> post;

  /**
   * Returns the postcondition for {@code impl}.
   */
  public Term getVc(Implementation impl) {
    Block entry = impl.getBody().getBlocks();
    assert false;
    // TODO Continue here
    return null;
  }

}
