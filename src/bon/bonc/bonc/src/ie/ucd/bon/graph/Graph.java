/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.graph;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map.Entry;

import com.google.common.collect.ForwardingMultimap;
import com.google.common.collect.LinkedListMultimap;
import com.google.common.collect.Multimap;

public class Graph<A,B> extends ForwardingMultimap<A,B> {

  private final Multimap<A,B> delegate;

  public Graph() {
    delegate = LinkedListMultimap.create();
  }

  @Override
  protected Multimap<A, B> delegate() {
    return delegate;
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
      Collection<B> nbs = get(a);
      if (nbs == null) { continue; }
      Collection<A> nas = converter.convert(nbs);
      if (nas == null) { continue; }
      for (A na : nas) {
        if (pred.get(na) == null) {
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
    }
    return null;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();

    for (Entry<A,B> edge : entries()) {
      sb.append(edge.getKey());
      sb.append(" -> ");
      sb.append(edge.getValue());
      sb.append("\n");
    }

    return sb.toString();
  }


}
