package b2bpl.graph;


public abstract class AbstractEdge<
    V extends AbstractVertex<V, E>,
    E extends AbstractEdge<V, E>> {

  protected final V source;

  protected final V target;

  protected boolean isBackEdge;

  public AbstractEdge(V source, V target) {
    this.source = source;
    this.target = target;
  }

  public V getSource() {
    return source;
  }

  public V getTarget() {
    return target;
  }

  public boolean isBackEdge() {
    return isBackEdge;
  }

  public void setBackEdge(boolean isBackEdge) {
    this.isBackEdge = isBackEdge;
  }
}
