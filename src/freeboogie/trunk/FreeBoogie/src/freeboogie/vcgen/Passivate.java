package freeboogie.vcgen;

import java.util.*;
import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.tc.*;
import freeboogie.util.*;

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
  private HashMap<VariableDecl, HashMap<Block, Integer>> readIdx;
  private HashMap<VariableDecl, HashMap<Block, Integer>> writeIdx;
  private HashMap<VariableDecl, Integer> newVarsCnt;
  private HashMap<Block, HashSet<VariableDecl>> blockWs;
  private ReadWriteSetFinder rwsf;

  private VariableDecl currentVar;
  private HashMap<Block, Integer> currentReadIdxCache;
  private HashMap<Block, Integer> currentWriteIdxCache;
  private SimpleGraph<Block> currentFG;

  // === public interface ===
  
  /** 
   * Instruct the passivator to use {@code bfgs} to retrieve
   * flow-graph information.
   */
  public void setFlowGraphs(BlockFlowGraphs bfgs) { flowGraphs = bfgs; }

  public Declaration process(Declaration ast, SymbolTable st) {
    readIdx = new LinkedHashMap<VariableDecl, HashMap<Block, Integer>>();
    writeIdx = new LinkedHashMap<VariableDecl, HashMap<Block, Integer>>();
    newVarsCnt = new HashMap<VariableDecl, Integer>();
    blockWs = new HashMap<Block, HashSet<VariableDecl>>();
    rwsf = new ReadWriteSetFinder(st);
    ast = (Declaration)ast.eval(this);
    // TODO Add new globals
    return ast;
  }

  // === (block) transformers ===

  @Override
  public Implementation eval(Implementation implementation, Signature sig, Body body, Declaration tail) {
    currentFG = flowGraphs.getFlowGraph(implementation);
    assert currentFG != null; // You should tell me the flowgraph beforehand
    assert !currentFG.hasCycle(); // You should cut cycles first

    // Collect all variables whose value potentially changes
    Pair<CSeq<VariableDecl>, CSeq<VariableDecl>> rwIds = 
      implementation.eval(rwsf);
    HashSet<VariableDecl> allIds = new HashSet<VariableDecl>();
    for (VariableDecl vd : rwIds.first) allIds.add(vd);

    for (VariableDecl vd : allIds) {
      currentVar = vd;
      currentReadIdxCache = new HashMap<Block, Integer>();
      currentWriteIdxCache = new HashMap<Block, Integer>();
      readIdx.put(vd, currentReadIdxCache);
      writeIdx.put(vd, currentWriteIdxCache);
      currentFG.iterNode(new Closure<Block>() {
        @Override public void go(Block b) {
          compReadIdx(b); compWriteIdx(b);
        }
      });
    }


    // TODO Add new locals
    if (tail != null) tail = (Declaration)tail.eval(this);
    return Implementation.mk(sig, body, tail);
  }


  // === workers ===

  private int compReadIdx(Block b) {
    if (currentReadIdxCache.containsKey(b))
      return currentReadIdxCache.get(b);
    int ri = -1;
    for (Block pre : currentFG.to(b))
      ri = Math.max(ri, compWriteIdx(pre));
    currentReadIdxCache.put(b, ri);
    return ri;
  }

  private int compWriteIdx(Block b) {
    if (currentWriteIdxCache.containsKey(b))
      return currentWriteIdxCache.get(b.getCmd());
    int wi = compReadIdx(b);
    HashSet<VariableDecl> ws = blockWs.get(b);
    if (ws == null) {
      ws = new HashSet<VariableDecl>();
      for (VariableDecl vd : rwsf.get(b).first) ws.add(vd);
      blockWs.put(b, ws);
    }
    if (ws.contains(currentVar)) ++wi;
    currentWriteIdxCache.put(b, wi);
    return wi;
  }

}
