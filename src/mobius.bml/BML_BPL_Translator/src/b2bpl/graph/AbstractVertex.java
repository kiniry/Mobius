package b2bpl.graph;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;


/**
 * Abstract class representing a vertex in a control flow graph.
 *
 * <p>
 * A vertex is basically characterized by a set of ingoing and outgoing edges
 * which are instances of the {@link AbstractEdge} class.
 * </p>
 *
 * @param <V>  A type parameter representing the concrete vertex to be used
 *             as a basic block in the control flow graph.
 * @param <E>  A type parameter representing the concrete edge to be used
 *             in the control flow graph.
 *
 * @see AbstractEdge
 * @see AbstractFlowGraph
 *
 * @author Ovidio Mallo
 */
public abstract class AbstractVertex<
    V extends AbstractVertex<V, E>,
    E extends AbstractEdge<V, E>> {

  /** The set of ingoing edges of this vertex. */
  protected List<E> inEdges;

  /** The set of outgoing edges of this vertex. */
  protected List<E> outEdges;

  /**
   * An identifier which can be set on the vertex to uniquely identify it.
   * Having such an identifier is convenient for many graph algorithms.
   */
  protected int id;

  /**
   * Creates a new vertex without any ingoing or outgoing edges.
   */
  public AbstractVertex() {
    inEdges = new ArrayList<E>();
    outEdges = new ArrayList<E>();
  }

  /**
   * Returns the identifier associated to this vertex.
   *
   * @return  The identifier associated to this vertex.
   */
  public int getID() {
    return id;
  }

  /**
   * Sets the identifier associated to this vertex.
   *
   * @param id  The identifier to associate to this vertex.
   */
  public void setID(int id) {
    this.id = id;
  }

  /**
   * Special method used to delegate the creation of a new predecessor edge for
   * this vertex to a concrete subclass. Such a method is necessary since Java
   * provides no runtime support for generics, meaning that we cannot directly
   * instantiate an object whose type is a type parameter.
   *
   * @param predecessor  The predecessor of this vertex.
   * @return             The newly created predecessor edge.
   */
  protected abstract E newPredecessorEdge(V predecessor);

  /**
   * Special method used to delegate the creation of a new successor edge for
   * this vertex to a concrete subclass. Such a method is necessary since Java
   * provides no runtime support for generics, meaning that we cannot directly
   * instantiate an object whose type is a type parameter.
   *
   * @param successor  The successor of this vertex.
   * @return           The newly created successor edge.
   */
  protected abstract E newSuccessorEdge(V successor);

  /**
   * Adds a new predecessor to this vertex. The set of predecessors of this
   * vertex as well as the set of successors of the given {@code predecessor}
   * will thereby be updated accordingly.
   *
   * @param predecessor  The new predecessor of this vertex.
   * @return             A new predecessor edge connecting the given
   *                     {@code predecessor} to this vertex.
   */
  public E addPredecessor(V predecessor) {
    E edge = newPredecessorEdge(predecessor);
    predecessor.outEdges.add(edge);
    inEdges.add(edge);
    return edge;
  }

  /**
   * Adds a new successor to this vertex. The set of successor of this
   * vertex as well as the set of predecessors of the given {@code successor}
   * will thereby be updated accordingly.
   *
   * @param successor  The new successor of this vertex.
   * @return           A new successor edge connecting the given
   *                   {@code successor} to this vertex.
   */
  public E addSuccessor(V successor) {
    E edge = newSuccessorEdge(successor);
    outEdges.add(edge);
    successor.inEdges.add(edge);
    return edge;
  }

  /**
   * Returns the number of predecessors of this vertex.
   *
   * @return  The number of predecessors of this vertex.
   */
  public int getPredecessorCount() {
    return inEdges.size();
  }

  /**
   * Returns the number of successors of this vertex.
   *
   * @return  The number of successors of this vertex.
   */
  public int getSuccessorCount() {
    return outEdges.size();
  }

  /**
   * Returns a list of predecessors of this vertex.
   *
   * @return  A list of predecessors of this vertex.
   */
  public List<V> getPredecessors() {
    List<V> predecessors = new ArrayList<V>();
    for (E inEdge : inEdges) {
      predecessors.add(inEdge.getSource());
    }
    return predecessors;
  }

  /**
   * Returns a list of successors of this vertex.
   *
   * @return  A list of successors of this vertex.
   */
  public List<V> getSuccessors() {
    List<V> successors = new ArrayList<V>();
    for (E outEdge : outEdges) {
      successors.add(outEdge.getTarget());
    }
    return successors;
  }

  /**
   * Returns whether this vertex has any predecessor.
   *
   * @return  Whether this vertex has any predecessor.
   */
  public boolean hasPredecessors() {
    return inEdges.size() > 0;
  }

  /**
   * Returns whether this vertex has any successor.
   *
   * @return  Whether this vertex has any successor.
   */
  public boolean hasSuccessors() {
    return outEdges.size() > 0;
  }

  /**
   * Returns whether the given {@code block} is a predecessor of this vertex.
   *
   * @param block  The eventual predecessor block.
   * @return       Whether the given {@code block} is a predecessor of this
   *               vertex.
   */
  public boolean isPredecessor(V block) {
    return getPredecessorEdge(block) != null;
  }

  /**
   * Returns whether the given {@code block} is a successor of this vertex.
   *
   * @param block  The eventual successor block.
   * @return       Whether the given {@code block} is a successor of this
   *               vertex.
   */
  public boolean isSuccessor(V block) {
    return getSuccessorEdge(block) != null;
  }

  /**
   * Returns the ingoing edge connecting the given {@code predecessor} to this
   * vertex or {@code null} if {@code predecessor} is not a predecessor of this
   * vertex.
   *
   * @param predecessor  The eventual predecessor of this vertex.
   * @return             The ingoing edge connecting the given
   *                     {@code predecessor} to this vertex or {@code null} if
   *                     {@code predecessor} is not a predecessor of this
   *                     vertex.
   */
  public E getPredecessorEdge(V predecessor) {
    for (E inEdge : inEdges) {
      if (inEdge.getSource() == predecessor) {
        return inEdge;
      }
    }
    return null;
  }

  /**
   * Returns the outgoing edge connecting the given {@code successor} to this
   * vertex or {@code null} if {@code successor} is not a successor of this
   * vertex.
   *
   * @param successor  The eventual successor of this vertex.
   * @return           The outgoing edge connecting the given
   *                   {@code successor} to this vertex or {@code null} if
   *                   {@code successor} is not a predecessor of this vertex.
   */
  public E getSuccessorEdge(V successor) {
    for (E outEdge : outEdges) {
      if (outEdge.getTarget() == successor) {
        return outEdge;
      }
    }
    return null;
  }

  /**
   * Returns whether this vertex is the target of a back edge.
   *
   * @return  Whether this vertex is the target of a back edge.
   */
  public boolean isBackEdgeTarget() {
    for (E inEdge : inEdges) {
      if (inEdge.isBackEdge()) {
        return true;
      }
    }
    return false;
  }

  /**
   * Returns an iterator for the ingoing edges of this vertex.
   *
   * @return  An iterator for the ingoing edges of this vertex.
   */
  public Iterator<E> inEdgeIterator() {
    return inEdges.iterator();
  }

  /**
   * Returns an iterator for the outgoing edges of this vertex.
   *
   * @return  An iterator for the outgoing edges of this vertex.
   */
  public Iterator<E> outEdgeIterator() {
    return outEdges.iterator();
  }

  /**
   * Returns an iterator for the predecessors of this vertex.
   *
   * @return  An iterator for the predecessors of this vertex.
   */
  public Iterator<V> predecessorIterator() {
    return new PredecessorIterator();
  }

  /**
   * Returns an iterator for the successors of this vertex.
   *
   * @return  An iterator for the successors of this vertex.
   */
  public Iterator<V> successorIterator() {
    return new SuccessorIterator();
  }

  /**
   * Simple iterator for the predecessors of this vertex. Uses an iterator for
   * the ingoing edges of this vertex to retrieve its predecessors.
   *
   * @author Ovidio Mallo
   */
  private final class PredecessorIterator implements Iterator<V> {

    /**
     * The iterator for the ingoing edges of the vertex used to retrieve the
     * vertex' predecessors.
     */
    private final Iterator<E> inEdgeIterator;

    /**
     * Initializes the iterator by getting the current in-edge iterator.
     */
    public PredecessorIterator() {
      this.inEdgeIterator = inEdgeIterator();
    }

    public boolean hasNext() {
      return inEdgeIterator.hasNext();
    }

    public V next() {
      return inEdgeIterator.next().getSource();
    }

    public void remove() {
      throw new UnsupportedOperationException();
    }
  }

  /**
   * Simple iterator for the successors of this vertex. Uses an iterator for
   * the outgoing edges of this vertex to retrieve its successors.
   *
   * @author Ovidio Mallo
   */
  private final class SuccessorIterator implements Iterator<V> {

    /**
     * The iterator for the outgoing edges of the vertex used to retrieve the
     * vertex' successors.
     */
    private final Iterator<E> outEdgeIterator;

    /**
     * Initializes the iterator by getting the current out-edge iterator.
     */
    public SuccessorIterator() {
      this.outEdgeIterator = outEdgeIterator();
    }

    public boolean hasNext() {
      return outEdgeIterator.hasNext();
    }

    public V next() {
      return outEdgeIterator.next().getTarget();
    }

    public void remove() {
      throw new UnsupportedOperationException();
    }
  }
}
