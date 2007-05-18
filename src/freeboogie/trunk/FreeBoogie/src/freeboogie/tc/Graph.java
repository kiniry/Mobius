/** Public domain. */

package freeboogie.tc;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

/**
 * Represents a graph of objects of type {@code N}. The implementation
 * uses adjacency lists and hash tables.
 *
 * @author rgrig 
 * @author reviewed by TODO
 * @param <N> the type of the graph node
 */
public class Graph<N> {
  private HashMap<N,HashSet<N>> parents = new HashMap<N,HashSet<N>>();
  private HashMap<N,HashSet<N>> children = new HashMap<N,HashSet<N>>();
  
  private void add(HashMap<N,HashSet<N>> m, N x, N y) {
    HashSet<N> s = m.get(x);
    if (s == null) s = new HashSet<N>();
    s.add(y);
    m.put(x, s);
  }
  
  /**
   * Adds an edge to the graph.
   * @param from the source
   * @param to the target
   */
  public void edge(N from, N to) {
    add(parents, from, to);
    add(children, to, from);
  }
  
  /**
   * Where can you go from {@code from}? The user shall not modify the
   * return value.
   * @param from the source
   * @return the tips of the out-edges
   */
  public Set<N> to(N from) {
    return children.get(from);
  }
  
  /**
   * From where can you get to {@code to}? The user shall not modify the
   * return value.
   * @param to the target
   * @return the sources of the in-edges
   */
  public Set<N> from(N to) {
    return parents.get(to);
  }
  
  /**
   * @param args
   */
  public static void main(String[] args) {
    // TODO Auto-generated method stub
  }

}
