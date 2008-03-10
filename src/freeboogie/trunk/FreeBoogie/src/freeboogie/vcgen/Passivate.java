package freeboogie.vcgen;

import java.util.*;
import java.util.logging.Logger;

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
 * variable. 
 *
 * Each variable X is transformed into a sequence of variables
 * X_0, X_1, ... Each command has a read index r and a write
 * index w (for each variable), meaning that reads from X will be
 * replaced by reads from X_r and a write to X is replaced by a
 * write to X_w.
 *
 * We have:
 *   r(n) = max_{m BEFORE n} w(m)
 *   w(n) = 1 + r(n)   if n writes to X
 *   w(n) = r(n)       otherwise
 *
 * Copy operations (assumes) need to be inserted when the value
 * written by a node is not the same as the one read by one of
 * its successors (according the the scheme above).
 *
 * All variables X, Y, ... inside old() are replaced 
 * by X_0, Y_0, ... and the old() is removed.
 *
 * This algorithm minimizes the number of variables (think
 * coloring of comparison graphs) but not the number of copy
 * operations.
 */
public class Passivate {
  // used mainly for debugging
  static private final Logger log = Logger.getLogger("freeboogie.vcgen");

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
