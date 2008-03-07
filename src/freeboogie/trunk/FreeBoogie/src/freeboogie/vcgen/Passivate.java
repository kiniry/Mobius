package freeboogie.vcgen;

import java.util.*;

import freeboogie.ast.*;
import freeboogie.tc.SimpleGraph;
import freeboogie.util.Closure;

/**
 * Constructs a {@code SimpleGraph<AssertAssumeCmd>} from
 * a {@code SimpleGraph<Command>} that contains no call
 * command. Havoc and assignment commands are transformed into
 * assumptions, by introducing extra variables. "Old" expressions
 * are also removed, using the same variables used to get rid of
 * assignments.
 *
 * Each `havoc' command is replaced by an assignment from a fresh
 * variable (havoc0, havoc1, ...)
 *
 * Each variable X is transformed into a sequence of variables
 * X_0, X_1, ... Each command has a read index r and a write
 * index w (for each variable), meaning that reads from X will be
 * replaced by reads from X_r and a write to X is replaced by a
 * write to X_w.
 *
 * TODO Check that a variable appers only once on the lhs of
 *      a parallel assignment.
 *
 * We have:
 *   r(n) = max_{m precedes n} w(m)
 *   w(n) = 1 + r(n)   if n writes to X
 *   w(n) = r(n)       otherwise
 *
 * Copy operations (assumes) need to be inserted when the value
 * written by a node is not the same as the one read by one of
 * its successors (according the the scheme above).
 *
 * "Old" expressions are simply removed and all variables X, Y, ...
 * are replaced by X_0, Y_0, ...
 *
 * This algorithm minimizes the number of variables (think
 * coloring of comparison graphs) but not the number of copy
 * operations.
 *
 * TODO How to make sure that the variables I create here are
 *      unique? (make AST utility for that)
 *
 * TODO This implementation is on hold while I write a couple
 *      of helper visitors: (1) to collect read/write identifiers,
 *      and (2) to operate a substitution an an AST.
 */
public class Passivate {
  private HashMap<String, HashMap<Command, Integer>> readIdx;
  private HashMap<String, HashMap<Command, Integer>> writeIdx;

  public SimpleGraph<AssertAssumeCmd> go(SimpleGraph<Command> flow) {
    SimpleGraph<AssertAssumeCmd> r = new SimpleGraph<AssertAssumeCmd>();
    readIdx = new LinkedHashMap<String, HashMap<Command, Integer>>();
    writeIdx = new LinkedHashMap<String, HashMap<Command, Integer>>();
    flow.iterNode(new Closure<Command>() {
      @Override
      public void go(Command cmd) {
        // TODO Continue here
      }
    });
    return r;
  }
}
