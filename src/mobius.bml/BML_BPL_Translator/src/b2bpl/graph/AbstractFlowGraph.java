package b2bpl.graph;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;


/**
 * Provides a simple implementation of a control flow graph.
 *
 * <p>
 * The vertices and edges in the control flow graph are represented by the
 * {@link AbstractVertex} and {@link AbstractEdge} classes, respectively.
 * In addition to providing a simple flow graph datastructure, this class also
 * implements algorithms for detecting loops and for determining some
 * structural properties of the flow graph such as whether it is reducible or
 * not.
 * </p>
 *
 * @param <V>  A type parameter representing the concrete vertex to be used
 *             as a basic block in the control flow graph.
 * @param <E>  A type parameter representing the concrete edge to be used
 *             in the control flow graph.
 *
 * @see AbstractVertex
 * @see AbstractEdge
 * 
 * @author Ovidio Mallo
 */
public abstract class AbstractFlowGraph<
    V extends AbstractVertex<V, E>,
    E extends AbstractEdge<V, E>> {

  /** The set of blocks constituing this control flow graph. */
  protected final List<V> blocks;

  /** A synthetic block in the graph at which the flow always starts. */
  protected final V entryBlock;

  /** A synthetic block in the graph at which the flow always ends. */
  protected final V exitBlock;

  /**
   * Whether this flow graph is reducible or not. The value of this flag can
   * only be relied on after having invoked the {@code analyze} method.
   */
  protected boolean isReducible;

  /**
   * Initializes the flow graph by creating the synthetic entry and exit blocks
   * and adding them to the set of blocks constituing the flow graph.
   */
  public AbstractFlowGraph() {
    blocks = new ArrayList<V>();
    entryBlock = newBlock();
    exitBlock = newBlock();
    addBlock(entryBlock);
    addBlock(exitBlock);
  }

  /**
   * Special method used to delegate the creation of a new block of the flow
   * graph to a concrete subclass. Such a method is necessary since
   * Java provides no runtime support for generics, meaning that we cannot
   * directly instantiate an object whose type is a type parameter.
   *
   * @return  The newly created block of the flow graph.
   */
  protected abstract V newBlock();

  /**
   * Returns the synthetic entry block of this control flow graph.
   *
   * @return  The synthetic entry block of this control flow graph.
   */
  public V getEntryBlock() {
    return entryBlock;
  }

  /**
   * Returns the synthetic exit block of this control flow graph.
   *
   * @return  The synthetic exit block of this control flow graph.
   */
  public V getExitBlock() {
    return exitBlock;
  }

  /**
   * Returns whether the given {@code block} is a synthetic block, that is,
   * whether it is the entry of the exit block of the control flow graph.
   *
   * @param block  The eventual synthetic block.
   * @return       Whether the given {@code block} is a synthetic block,
   *               that is, whether it is the entry of the exit block of the
   *               control flow graph.
   */
  public boolean isSyntheticBlock(V block) {
    return (block == entryBlock) || (block == exitBlock);
  }

  /**
   * Adds the given {@code block} to the set of blocks constituing this flow
   * graph and gives it a unique identifier which should never be modified from
   * outside this flow graph.
   *
   * @param block  The block to add to the flow graph.
   */
  public void addBlock(V block) {
    block.setID(blocks.size());
    blocks.add(block);
  }

  /**
   * Returns the number of blocks in this flow graph, including the synthetic
   * entry and exit blocks.
   *
   * @return  The number of blocks in this flow graph, including the synthetic
   *          entry and exit blocks.
   */
  public int getBlockCount() {
    return blocks.size();
  }

  /**
   * Returns an iterator for the blocks of this flow graph, including the
   * synthetic entry and exit blocks.
   *
   * @return  An iterator for the blocks of this flow graph, including the
   *          synthetic entry and exit blocks.
   */
  public Iterator<V> blockIterator() {
    return blocks.iterator();
  }

  /**
   * Analyzes this flow graph by marking every back edge as such and by checking
   * whether the graph is reducible or not. Once this method has terminated,
   * those properties can be quieried reliably on the corresponding edges and
   * on this graph, respectively.
   *
   * @see AbstractEdge#isBackEdge()
   * @see #isReducible()
   */
  public void analyze() {
    markBackEdges();
    checkForReducibility();
  }

  /**
   * Computes all the back edges in this flow graph and marks them as such. This
   * requires a dominator analysis to be performed.
   *
   * <p>
   * For the dominator analysis, a simple iterative algorithm (as described in
   * the "Dragon Book") is employed which works as follows:
   * <ul>
   *   <li>
   *     The dominator set of the synthetic entry block of the graph is
   *     initialized to contain itself only while the dominator sets of all
   *     other blocks are initialized to contain all blocks of the graph.
   *   </li>
   *   <li>
   *     Some block can only be a dominator of another block if it is the same
   *     block or if it also dominates all the predecessors of that block.
   *     Therefore, the dominator analysis can be performed iteratively by
   *     continuely replacing a block's dominator set by the intersection of the
   *     dominator sets of all its predecessors, or else, by the block itself in
   *     case it has no predecessors.
   *   </li>
   * </ul>
   * Once the dominator analysis has been performed, all the edges whose target
   * block dominates the source block are marked as back edges.
   * </p>
   *
   * @see AbstractEdge#isBackEdge()
   * @see AbstractEdge#setBackEdge(boolean)
   */
  private void markBackEdges() {
    // Initialize the set of dominators for every block in the graph.
    BitSet[] dominators = new BitSet[blocks.size()];
    for (int i = 0; i < dominators.length; i++) {
      dominators[i] = new BitSet(blocks.size());
      if (blocks.get(i) == entryBlock) {
        // The entry block is dominated by itself only.
        dominators[i].set(entryBlock.getID());
      } else {
        // All other blocks but the entry block are initialized to be dominated
        // by all blocks in the graph.
        dominators[i].set(0, blocks.size());
      }
    }

    // Iteratively adapt the dominator sets of the individual blocks.
    boolean changed;
    do {
      // Track whether anything has changed in the dominator set of any block.
      changed = false;
      for (V block : blocks) {
        // The new dominator set to associate the current block.
        BitSet newDominators = new BitSet(blocks.size());
        if (block.hasPredecessors()) {
          // Set all bits of the dominator set before computing the intersection
          // of the dominator sets of the block's predecessors.
          newDominators.set(0, blocks.size());
          for (Iterator<E> iter = block.inEdgeIterator(); iter.hasNext(); ) {
            V predecessor = iter.next().getSource();
            newDominators.and(dominators[predecessor.getID()]);
          }
        }
        // A block always dominates itself.
        newDominators.set(block.getID());
        // Check whether anything has changed in the dominator set.
        changed = changed || !newDominators.equals(dominators[block.getID()]);
        dominators[block.getID()] = newDominators;
      }
    } while (changed);

    // Correctly categorize all the edges as back edges or forward edges.
    for (V block : blocks) {
      for (Iterator<E> iter = block.outEdgeIterator(); iter.hasNext(); ) {
        E outEdge = iter.next();
        // An edge is a back edge if and only if its target block dominates its
        // source block.
        V successor = outEdge.getTarget();
        outEdge.setBackEdge(dominators[block.getID()].get(successor.getID()));
      }
    }
  }

  /**
   * Checks whether this flow graph is reducible or not and sets the
   * {@code isReducible} flag accordingly. This method relies on all the edges
   * of this flow graph being correctly categorized as back edges or not.
   *
   * @see #markBackEdges()
   * @see #isReducible()
   */
  private void checkForReducibility() {
    // The graph is set to be reducible as long as we do not detect any loop
    // along forward edges below.
    isReducible = true;
    // Check for loops along forward edges starting at the entry block.
    checkForReducibility(entryBlock, new BitSet(blocks.size()));
  }

  /**
   * Recursively checks whether this flow graph is reducible or not and sets the
   * {@code isReducible} flag accordingly. This method relies on all the edges
   * of this flow graph being correctly categorized as back edges or not.
   *
   * <p>
   * One of the definitions of reducibility of a directed graph is that the
   * graph is reducible if and only if its set of <i>forward</i> edges contains
   * a loop. Therefore, this method checks for the reducibility property by
   * following the forward edges of this graph only (and simply
   * <i>neglecting</i> the back edges instead of really removing them from the
   * graph) and checking whether any loop is encountered in which case the
   * graph is <i>not</i> reducible.
   * </p>
   *
   * @param block  The vertex in the graph whose successors along forward edges
   *               are to be visited next.
   * @param path   A bitset marking the set of vertices which have already been
   *               visited along the current path. This is used to detect
   *               whether we are visiting a vertex twice along the same path in
   *               which case we would have detected a loop.
   *
   * @see #markBackEdges()
   * @see #isReducible()
   * @see AbstractVertex#getID()
   */
  private void checkForReducibility(V block, BitSet path) {
    if (path.get(block.getID())) {
      // If the current block has already been visited along the current path,
      // we have detected a loop along forward edges meaning that the graph is
      // not reducible.
      isReducible = false;
    } else {
      // Visit the current block and all its successors along forward edges.
      path.set(block.getID());
      for (Iterator<E> iter = block.outEdgeIterator(); iter.hasNext(); ) {
        E outEdge = iter.next();
        // Only follow forward edges.
        if (!outEdge.isBackEdge()) {
          checkForReducibility(outEdge.getTarget(), path);
        }
      }
      // All paths starting at the current block must have been explored
      // recursively by now so we can clear the bit of the current block on
      // the current path and backtrack.
      path.clear(block.getID());
    }
  }

  /**
   * Returns whether this flow graph is reducible or not. The value of this
   * flag can only be relied on after having invoked the {@code analyze} method.
   *
   * @return  Whether this flow graph is reducible or not.
   *
   * @see #analyze()
   */
  public boolean isReducible() {
    return isReducible;
  }

  /**
   * Computes the set of vertices contained in the natural loop defined by the
   * given {@code backEdge}. The vertices are returned in no particular order.
   *
   * @param backEdge  The back edge defining the natural loop.
   * @return          The set of vertices contained in the natural loop defined
   *                  by the given {@code backEdge}.
   */
  public HashSet<V> computeNaturalLoop(E backEdge) {
    HashSet<V> loopBlocks = new HashSet<V>();
    // Add the loop header to the loop blocks.
    loopBlocks.add(backEdge.getTarget());
    // Start accumulating other blocks inside the loop by starting at the source
    // of the back edge and visiting all its predecessors until we get to the
    // loop header again.
    accumLoopBlocks(loopBlocks, backEdge.getSource());
    return loopBlocks;
  }

  /**
   * Adds the given block {@code next} to the {@code loopBlocks} and, if that
   * block was not already contained in the set of loop blocks, all its
   * predecessors are recursively added to the set of loop blocks as well.
   *
   * @param loopBlocks  The set of loop blocks being accumulated.
   * @param next        The next block to add to the loop blocks.
   */
  private void accumLoopBlocks(HashSet<V> loopBlocks, V next) {
    // If the block is new, we recurse on all its predecessors.
    if (loopBlocks.add(next)) {
      for (Iterator<E> iter = next.inEdgeIterator(); iter.hasNext(); ) {
        accumLoopBlocks(loopBlocks, iter.next().getSource());
      }
    }
  }
}
