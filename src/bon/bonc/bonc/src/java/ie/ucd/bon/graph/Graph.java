/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.graph;

import ie.ucd.bon.util.Converter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import com.google.common.collect.ForwardingMultimap;
import com.google.common.collect.LinkedListMultimap;
import com.google.common.collect.Multimap;

public class Graph<A,B> extends ForwardingMultimap<A,B> {

  private final Multimap<A,B> delegate;
  private final Multimap<B,A> reverse;

  public Graph() {
    delegate = LinkedListMultimap.create();
    reverse = LinkedListMultimap.create();
  }

  @Override
  protected Multimap<A, B> delegate() {
    return delegate;
  }

  @Override
  public boolean put(A key, B value) {
    reverse.put(value, key);
    return super.put(key, value);
  }

  @Override
  public boolean remove(Object key, Object value) {
    reverse.remove(value, key);
    return super.remove(key, value);
  }
  
  public Multimap<B,A> reverse() {
    return reverse;
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
  
  public final List<A> findPath(A startNode, A endNode, Converter<B,A> converter) {
    if (startNode.equals(endNode)) {
      List<A> single = new ArrayList<A>();
      single.add(startNode);
      return single;
    }

    Map<A,A> pred = new HashMap<A,A>();
    
    LinkedList<A> todo = new LinkedList<A>();
    todo.addLast(startNode);
    while(!todo.isEmpty()) {
      A current = todo.removeFirst();
      Collection<B> nexts = get(current);
      if (nexts == null) {
        continue;
      }
      Collection<A> nextAs = converter.convert(nexts);
      if (nextAs == null) {
        continue;
      }
      for (A nextA : nextAs) {
        if (pred.get(nextA) == null) {
          if (nextA.equals(endNode)) {
            // build and return path
            LinkedList<A> result = new LinkedList<A>();
            result.addFirst(nextA);
            result.addFirst(current);
            while (current != startNode) {
              current = pred.get(current);
              result.addFirst(current);
            }
            return result;
          }
          pred.put(nextA, current);
          todo.addLast(nextA);
        }
      }
    }
    return null;
  }
  
  public Set<A> getAllSuccessorNodes(A startNode, Converter<B,A> converter) {
    return internalGetAllSuccessorNodes(startNode, converter, new LinkedHashSet<A>());
  }
  
  private Set<A> internalGetAllSuccessorNodes(A startNode, Converter<B,A> converter, Set<A> seen) {
    Collection<A> linked = converter.convert(get(startNode));
    for (A a : linked) {
      if (!seen.contains(a)) {
        seen.add(a);
        internalGetAllSuccessorNodes(a, converter, seen);
      }
    }    
    return seen;
  }
  
  public Set<A> getAllPredecessorNodes(A startNode, Converter<A,B> converter) {
    return internalGetAllPredecessorNodes(startNode, converter, new LinkedHashSet<A>());
  }
  
  private Set<A> internalGetAllPredecessorNodes(A startNode, Converter<A,B> converter, Set<A> seen) {
    Collection<A> linked = reverse().get(converter.convert(startNode));
    for (A a : linked) {
      if (!seen.contains(a)) {
        seen.add(a);
        internalGetAllPredecessorNodes(a, converter, seen);
      }
    }    
    return seen;
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
  
  public String toString(Converter<A,String> aConverter, Converter<B,String> bConverter) {
    StringBuilder sb = new StringBuilder();

    for (Entry<A,B> edge : entries()) {
      sb.append(aConverter.convert(edge.getKey()));
      sb.append(" -> ");
      sb.append(bConverter.convert(edge.getValue()));
      sb.append("\n");
    }

    return sb.toString();
  }


}
