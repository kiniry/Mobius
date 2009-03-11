/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.graph;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

public class Graph<A,B> {
  private static final boolean REMOVE_EDGES_TO_EMPTY_SET = true;
  
  private final HashMap<A,Set<B>> edges;
  
  public Graph() {
    edges = new HashMap<A,Set<B>>();
  }
  
  public final void addEdge(final A from, final B to) {
    Set<B> bs = edges.get(from);
    if (bs == null) {
      bs = new HashSet<B>();
      edges.put(from, bs);
    }
    bs.add(to);
  }
  
  public boolean removeEdge(final A from, final B to) {
    Set<B> bs = edges.get(from);
    if (bs != null) {
      boolean success = bs.remove(to);
      if (success && REMOVE_EDGES_TO_EMPTY_SET && bs.size() == 0) {
        edges.remove(from);
      }
      return success;
    } else {
      return false;
    }
  }
  
  public final boolean hasEdge(final A from) {
    return edges.containsKey(from);
  }
  
  public final boolean hasEdge(final A from, final B to) {
    Set<B> bs = edges.get(from);
    return bs==null ? false : bs.contains(to);
  }
  
  public final Set<B> getLinkedNodes(final A from) {
    Set<B> result = edges.get(from);
    return result == null ? new HashSet<B>() : result;
  }
  
  public final Set<A> getStartingNodes() {
    return edges.keySet();
  }

  /**
   * Returns one of the shortest cycles containing {@code startNode}
   * or {@code null} if no such cycle exists. Algorithm: BFS (so
   * the complexity is O(V+E)).
   *
   * NOTE: It is asymptotically faster to find cycles in one go rather
   *       than repeatedly calling this function for each node.
   */
  public final Collection<A> findCycle(A startNode, Converter<B,A> converter) {
    HashMap<A,A> pred = new HashMap<A,A>();
    LinkedList<A> todo = new LinkedList<A>(); // should be ArrayDeque in Java 6
    todo.addLast(startNode);
    while (!todo.isEmpty()) {
      A a = todo.removeFirst();
      Set<B> nbs = edges.get(a);
      if (nbs == null) continue;
      Set<A> nas = converter.convert(nbs);
      for (A na : nas) if (pred.get(na) == null) {
        if (na.equals(startNode)) {
          // build and return cycle
          LinkedList<A> result = new LinkedList<A>();
          result.addFirst(na); 
          result.addFirst(a);
          while (a != startNode) {
            a = pred.get(a);
            result.addFirst(a);
          }
          return result;
        }
        pred.put(na, a);
        todo.addLast(na);
      }
    }
    return null;
  }
  
  public Set<Map.Entry<A, Set<B>>> getEdges() {
    return edges.entrySet();
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    
    for (Entry<A,Set<B>> edge : edges.entrySet()) {
      sb.append(edge.getKey());
      sb.append(" -> ");
      sb.append(edge.getValue());
      sb.append("\n");
    }
    
    return sb.toString();
  }
  
  
}
