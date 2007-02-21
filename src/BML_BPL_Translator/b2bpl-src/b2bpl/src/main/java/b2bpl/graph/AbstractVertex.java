package b2bpl.graph;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;


public abstract class AbstractVertex<
    V extends AbstractVertex<V, E>,
    E extends AbstractEdge<V, E>> {

  protected List<E> inEdges;

  protected List<E> outEdges;

  protected int id;

  public AbstractVertex() {
    inEdges = new ArrayList<E>();
    outEdges = new ArrayList<E>();
  }

  public int getID() {
    return id;
  }

  public void setID(int id) {
    this.id = id;
  }

  protected abstract E newPredecessorEdge(V predecessor);

  protected abstract E newSuccessorEdge(V successor);

  public E addPredecessor(V predecessor) {
    E edge = newPredecessorEdge(predecessor);
    predecessor.outEdges.add(edge);
    inEdges.add(edge);
    return edge;
  }

  public E addSuccessor(V successor) {
    E edge = newSuccessorEdge(successor);
    outEdges.add(edge);
    successor.inEdges.add(edge);
    return edge;
  }

  public int getPredecessorCount() {
    return inEdges.size();
  }

  public int getSuccessorCount() {
    return outEdges.size();
  }

  public List<V> getPredecessors() {
    List<V> predecessors = new ArrayList<V>();
    for (E inEdge : inEdges) {
      predecessors.add(inEdge.getSource());
    }
    return predecessors;
  }

  public List<V> getSuccessors() {
    List<V> successors = new ArrayList<V>();
    for (E outEdge : outEdges) {
      successors.add(outEdge.getTarget());
    }
    return successors;
  }

  public boolean hasPredecessors() {
    return inEdges.size() > 0;
  }

  public boolean hasSuccessors() {
    return outEdges.size() > 0;
  }

  public boolean isPredecessor(V block) {
    return getPredecessorEdge(block) != null;
  }

  public boolean isSuccessor(V block) {
    return getSuccessorEdge(block) != null;
  }

  public E getPredecessorEdge(V predecessor) {
    for (E inEdge : inEdges) {
      if (inEdge.getSource() == predecessor) {
        return inEdge;
      }
    }
    return null;
  }

  public E getSuccessorEdge(V successor) {
    for (E outEdge : outEdges) {
      if (outEdge.getTarget() == successor) {
        return outEdge;
      }
    }
    return null;
  }

  public boolean isBackEdgeTarget() {
    for (E inEdge : inEdges) {
      if (inEdge.isBackEdge()) {
        return true;
      }
    }
    return false;
  }

  public Iterator<E> inEdgeIterator() {
    return inEdges.iterator();
  }

  public Iterator<E> outEdgeIterator() {
    return outEdges.iterator();
  }

  public Iterator<V> predecessorIterator() {
    return new PredecessorIterator(inEdgeIterator());
  }

  public Iterator<V> successorIterator() {
    return new SuccessorIterator(outEdgeIterator());
  }

  private final class PredecessorIterator implements Iterator<V> {

    private final Iterator<E> inEdgeIterator;

    public PredecessorIterator(Iterator<E> inEdgeIterator) {
      this.inEdgeIterator = inEdgeIterator;
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

  private final class SuccessorIterator implements Iterator<V> {

    private final Iterator<E> outEdgeIterator;

    public SuccessorIterator(Iterator<E> outEdgeIterator) {
      this.outEdgeIterator = outEdgeIterator;
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
