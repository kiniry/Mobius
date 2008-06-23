package freeboogie.vcgen;

import java.util.*;
import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.tc.*;
import freeboogie.util.Closure;

/**
 * Gets rid of assignments and "old" expressions by introducing 
 * new variables. We assume that
 *   (1) specs are desugared,
 *   (2) calls are desugared,
 *   (3) havocs are desugared,
 *   (4) the flowgraphs are computed and have no cycles.
 *
 * Each variable X is transformed into a sequence of variables
 * X, X_1, X_2, ... Each command has a read index r and a write
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
 * The "old()" is simply stripped.
 *
 * This algorithm minimizes the number of variables (think
 * coloring of comparison graphs) but not the number of copy
 * operations.
 *
 * @author rgrig
 */
public class Passivate extends Transformer {
  // used mainly for debugging
  static private final Logger log = Logger.getLogger("freeboogie.vcgen");

  private BlockFlowGraphs flowGraphs;
  private HashMap<VariableDecl, HashMap<Command, Integer>> readIdx;
  private HashMap<VariableDecl, HashMap<Command, Integer>> writeIdx;

  // === public interface ===

  /** 
   * Instruct the passivator to use {@code bfgs} to retrieve
   * flow-graph information.
   */
  public void setFlowGraphs(BlockFlowGraphs bfgs) { flowGraphs = bfgs; }

  public Declaration process(Declaration ast) {
    readIdx = new LinkedHashMap<VariableDecl, HashMap<Command, Integer>>();
    writeIdx = new LinkedHashMap<VariableDecl, HashMap<Command, Integer>>();
    return (Declaration)ast.eval(this);
  }

  // === (block) transformers ===

  @Override
  public Implementation eval(Implementation implementation, Signature sig, Body body, Declaration tail) {
    SimpleGraph<Block> fg = flowGraphs.getFlowGraph(implementation);
    assert fg != null; // You should tell me the flowgraph beforehand
    assert !fg.hasCycle(); // You should cut cycles first


    if (tail != null) tail = (Declaration)tail.eval(this);
    return Implementation.mk(sig, body, tail);
  }

}
