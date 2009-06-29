package freeboogie.tc;

import java.util.*;
import java.util.HashSet;
import java.util.Set;

import genericutils.Err;
import genericutils.SimpleGraph;

import freeboogie.ast.*;

/**
 * Constructs a flowgraph of blocks for each implementation.
 *
 * @author rgrig 
 */
@SuppressWarnings("unused") // unused params
public class BlockFlowGraphs extends Transformer {
  // finds blocks (in the currently processed Body) by name
  private HashMap<String, Block> blocksByName;
  
  // the flow graph currently being built
  private SimpleGraph<Block> currentFlowGraph;
  
  // the block currently being processed
  private Block currentBlock;
  
  // maps implementations to the flow graphs of their bodies
  private HashMap<Body, SimpleGraph<Block>> flowGraphs;
  
  // the detected problems 
  private List<FbError> errors;
  
  // used for reachability (DFS)
  private HashSet<Block> seenBlocks;
  
  // === public interface ===
  
  /**
   * Constructs flow graphs for {@code ast}. It also prints warnings
   * if there are syntactically unreachable blocks. 
   * @param ast the AST for which to build flow graphs
   * @return the detected problems 
   */
  public List<FbError> process(Declaration ast) {
    currentBlock = null;
    errors = new ArrayList<FbError>();
    flowGraphs = new HashMap<Body, SimpleGraph<Block>>();
    ast.eval(this);
    for (SimpleGraph<Block> fg : flowGraphs.values())
      fg.freeze();
    return errors;
  }
  
  /**
   * Returns the block flow graph for {@code impl}.
   * @param impl the implementation
   * @return the flow graph fro {@code impl}
   * @deprecated replaced by {@link #getFlowGraph(Body)}
   */
  @Deprecated
  public SimpleGraph<Block> getFlowGraph(Implementation impl) {
    return flowGraphs.get(impl.getBody());
  }
  
  /**
   * Returns the block flow graph for {@code bdy}.
   * @param bdy the body
   * @return the flow graph from {@code bdy}
   */
  public SimpleGraph<Block> getFlowGraph(Body bdy) {
    return flowGraphs.get(bdy);
  }
  
  
  // === helpers ===
  
  private void dfs(Block b) {
    if (seenBlocks.contains(b)) return;
    seenBlocks.add(b);
    Set<Block> children = currentFlowGraph.to(b);
    for (Block c : children) dfs(c); 
  }
  
  // === visiting methods ===
  
  @Override
  public void see(
    Implementation implementation,
    Attribute attr,
    Signature sig,
    Body body,
    Declaration tail
  ) {
    // initialize graph
    currentFlowGraph = new SimpleGraph<Block>();
    flowGraphs.put(implementation.getBody(), currentFlowGraph);
    
    // get blocks by name
    blocksByName = new HashMap<String, Block>();
    Block b = body.getBlocks();
    while (b != null) {
      blocksByName.put(b.getName(), b);
      currentFlowGraph.node(b);
      b = b.getTail();
    }
    
    // build graph
    body.eval(this);
    
    // check for reachability
    seenBlocks = new HashSet<Block>();
    b = body.getBlocks();
    if (b == null) return;
    dfs(b);
    while (b != null) {
      if (!seenBlocks.contains(b)) 
        Err.warning("" + b.loc() + ": Block " + b.getName() + " is unreachable.");
      b = b.getTail();
    }
    
    if (tail != null) tail.eval(this);
  }
  
  @Override
  public void see(Block block, String name, Command cmd, Identifiers succ, Block tail) {
    currentBlock = block;
    if (succ != null) succ.eval(this);
    currentBlock = null;
    if (tail != null) tail.eval(this);
  }
  
  @Override
  public void see(AtomId atomId, String id, TupleType types) {
    if (currentBlock == null) return;
    assert types == null;
    Block target = blocksByName.get(id);
    if (target == null)
      errors.add(new FbError(FbError.Type.MISSING_BLOCK, atomId, id));
    else
      currentFlowGraph.edge(currentBlock, target);
  }
}
