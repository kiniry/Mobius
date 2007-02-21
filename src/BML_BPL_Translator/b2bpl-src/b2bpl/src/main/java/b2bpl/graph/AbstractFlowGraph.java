package b2bpl.graph;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;


public abstract class AbstractFlowGraph<
    V extends AbstractVertex<V, E>,
    E extends AbstractEdge<V, E>> {

  protected final List<V> blocks;

  protected final V entryBlock;

  protected final V exitBlock;

  protected boolean isReducible;

  public AbstractFlowGraph() {
    blocks = new ArrayList<V>();
    entryBlock = newBlock();
    exitBlock = newBlock();
    addBlock(entryBlock);
    addBlock(exitBlock);
  }

  protected abstract V newBlock();

  public V getEntryBlock() {
    return entryBlock;
  }

  public V getExitBlock() {
    return exitBlock;
  }

  public boolean isSyntheticBlock(V block) {
    return (block == entryBlock) || (block == exitBlock);
  }

  public void addBlock(V block) {
    block.setID(blocks.size());
    blocks.add(block);
  }

  public int getBlockCount() {
    return blocks.size();
  }

  public Iterator<V> blockIterator() {
    return blocks.iterator();
  }

  public void analyze() {
    markBackEdges();
    checkForReducibility();
  }

  private void markBackEdges() {
    BitSet[] dominators = new BitSet[blocks.size()];
    for (int i = 0; i < dominators.length; i++) {
      dominators[i] = new BitSet(blocks.size());
      if (blocks.get(i) == entryBlock) {
        dominators[i].set(entryBlock.getID());
      } else {
        dominators[i].set(0, blocks.size());
      }
    }

    boolean changed;
    do {
      changed = false;
      for (V block : blocks) {
        BitSet newDominators = new BitSet(blocks.size());
        if (block.hasPredecessors()) {
          newDominators.set(0, blocks.size());
          for (Iterator<E> iter = block.inEdgeIterator(); iter.hasNext(); ) {
            V predecessor = iter.next().getSource();
            newDominators.and(dominators[predecessor.getID()]);
          }
        }
        newDominators.set(block.getID());
        changed = changed || !newDominators.equals(dominators[block.getID()]);
        dominators[block.getID()] = newDominators;
      }
    } while (changed);

    for (V block : blocks) {
      for (Iterator<E> iter = block.outEdgeIterator(); iter.hasNext(); ) {
        E outEdge = iter.next();
        V successor = outEdge.getTarget();
        outEdge.setBackEdge(dominators[block.getID()].get(successor.getID()));
      }
    }
  }

  private void checkForReducibility() {
    isReducible = true;
    checkForReducibility(entryBlock, new BitSet(blocks.size()));
  }

  private void checkForReducibility(V block, BitSet path) {
    if (path.get(block.getID())) {
      isReducible = false;
    } else {
      path.set(block.getID());
      for (Iterator<E> iter = block.outEdgeIterator(); iter.hasNext(); ) {
        E outEdge = iter.next();
        if (!outEdge.isBackEdge()) {
          checkForReducibility(outEdge.getTarget(), path);
        }
      }
      path.clear(block.getID());
    }
  }

  public boolean isReducible() {
    return isReducible;
  }

  public HashSet<V> computeNaturalLoop(E backEdge) {
    HashSet<V> loopBlocks = new HashSet<V>();
    loopBlocks.add(backEdge.getTarget());
    accumLoopBlocks(loopBlocks, backEdge.getSource());
    return loopBlocks;
  }

  private void accumLoopBlocks(HashSet<V> loopBlocks, V next) {
    if (loopBlocks.add(next)) {
      for (Iterator<E> iter = next.inEdgeIterator(); iter.hasNext(); ) {
        accumLoopBlocks(loopBlocks, iter.next().getSource());
      }
    }
  }
}
