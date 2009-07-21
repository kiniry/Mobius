package b2bpl.graph;


/**
 * Abstract class representing an edge in a control flow graph.
 *
 * <p>
 * An edge is basically characterized by its source and target vertices both
 * instances of the {@link AbstractVertex} class. In addition, the property
 * whether the edge is a back edge or not can be set and queried directly on
 * the edge itself for convenience.
 * </p>
 *
 * @param <V>  A type parameter representing the concrete vertex to be used
 *             as a basic block in the control flow graph.
 * @param <E>  A type parameter representing the concrete edge to be used
 *             in the control flow graph.
 *
 * @see AbstractVertex
 * @see AbstractFlowGraph
 *
 * @author Ovidio Mallo
 */
public abstract class AbstractEdge<
    V extends AbstractVertex<V, E>,
    E extends AbstractEdge<V, E>> {

  /** The source vertex of this edge. */
  protected final V source;

  /** The target vertex of this edge. */
  protected final V target;

  /** Whether this edge is a back edge or not. */
  protected boolean isBackEdge;

  /**
   * Sets the {@code source} and {@code target} basic blocks of the edge being
   * created.
   *
   * @param source  The source vertex of the edge being created.
   * @param target  The target vertex of the edge being created.
   */
  public AbstractEdge(V source, V target) {
    this.source = source;
    this.target = target;
  }

  /**
   * Returns the source vertex of this edge.
   *
   * @return  The source vertex of this edge.
   */
  public V getSource() {
    return source;
  }

  /**
   * Returns the target vertex of this edge.
   *
   * @return  The target vertex of this edge.
   */
  public V getTarget() {
    return target;
  }

  /**
   * Returns whether this edge is a back edge or not.
   *
   * @return  Whether this edge is a back edge or not.
   */
  public boolean isBackEdge() {
    return isBackEdge;
  }

  /**
   * Sets whether this edge is a back edge or not.
   *
   * @param isBackEdge  Whether this edge is a back edge or not.
   */
  public void setBackEdge(boolean isBackEdge) {
    this.isBackEdge = isBackEdge;
  }
}
