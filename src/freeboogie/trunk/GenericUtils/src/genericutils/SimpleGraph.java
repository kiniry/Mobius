package genericutils;

import java.util.*;

/**
 * Represents a graph of objects of type {@code N}. The implementation
 * uses adjacency lists and hash tables. Nodes are compared using
 * {@code equals()} rather than using {@code ==}.
 *
 * @author rgrig 
 * @param <N> the type of the graph node
 */
public class SimpleGraph<N> {
  private HashMap<N,HashSet<N>> parents;
  private HashMap<N,HashSet<N>> children;
  private boolean frozen;
  
  /** Construct an empty graph. */
  public SimpleGraph() {
    parents = new LinkedHashMap<N,HashSet<N>>();
    children = new LinkedHashMap<N,HashSet<N>>();
    frozen = false;
  }
  
  /**
   * Adds a node to the graph. Does nothing if the node is already
   * in the graph.
   * @param n the node to add to the graph
   */
  public void node(N n) {
    assert !frozen;
    assert parents.size() == children.size();
    if (parents.containsKey(n)) return;
    parents.put(n, new LinkedHashSet<N>());
    children.put(n, new LinkedHashSet<N>());
  }
  
  /**
   * Adds an edge to the graph.
   * @param from the source
   * @param to the target
   */
  public void edge(N from, N to) {
    assert !frozen;
    node(from); node(to);
    parents.get(to).add(from);
    children.get(from).add(to);
  }

  /**
   * Disallow future changes to the graph.
   */
  public void freeze() {
    frozen = true;
  }

  /**
   * Returns whether this graph is imutable.
   */
  public boolean isFrozen() {
    return frozen;
  }
  
  /**
   * Where can you go from {@code from}? The user shall not modify the
   * return value.
   * @param from the source, must be in this graph
   * @return the tips of the out-edges
   */
  public Set<N> to(N from) {
    return children.get(from);
  }
  
  /**
   * From where can you get to {@code to}? The user shall not modify the
   * return value.
   * @param to the target, must be in this graph
   * @return the sources of the in-edges
   */
  public Set<N> from(N to) {
    return parents.get(to);
  }

  // used for cycle detection and topological sorting
  private HashSet<N> seen;
  private HashSet<N> done;
  private List<N> sortedNodes;

  private boolean recHasCycle(N n) {
    if (done.contains(n)) return false;
    if (seen.contains(n)) return true;
    seen.add(n);
    for (N np : parents.get(n))
      if (recHasCycle(np)) return true;
    done.add(n);
    return false;
  }
 
  /**
   * Returns whether this graph contains any cycle.
   */
  public boolean hasCycle() {
    seen = new HashSet<N>();
    done = new HashSet<N>();
    for (N n : parents.keySet()) 
      if (recHasCycle(n)) return true;
    return false;
  }

  private void recTopologicalSort(N n) {
    if (seen.contains(n)) return;
    seen.add(n);
    for (N m : from(n)) recTopologicalSort(m);
    sortedNodes.add(n);
  }

  /** Returns all the nodes of this graph sorted topologically. */
  public List<N> nodesInTopologicalOrder() {
    seen = new HashSet<N>();
    sortedNodes = new ArrayList<N>();
    for (N n : parents.keySet()) recTopologicalSort(n);
    return sortedNodes;
  }
  
  /**
   * Execute {@code f} on all nodes, in a random order.
   * @param f the function to execute on all nodes
   */
  public void iterNode(Closure<N> f) {
    for (N n : parents.keySet()) f.go(n);
  }

  /**
   * Execute {@code f} on all edges, in a random order.
   * @param f the function to execute on all nodes
   */
  public void iterEdge(Closure<Pair<N,N>> f) {
    for (Map.Entry<N, HashSet<N>> a : parents.entrySet())
      for (N b : a.getValue()) f.go(Pair.of(b, a.getKey()));
  }
}
