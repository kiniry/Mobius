/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.graph;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

public class Graph<A,B> {
  
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
   * NOTE: It is asymptotcally faster to find cycles in one go rather
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
  
/*  public final Collection<A> findCycle(A startNode, Converter<B,A> converter) {
    Stack<A> currentPath = new Stack<A>(); //Stores the path we are currently exploring
    Stack<SortedSet<A>> waitingPaths = new Stack<SortedSet<A>>(); //Stores the alternative choices at each step
    
    Set<A> explored = new HashSet<A>(); //Store all explored 
    
    //Initially our path is just our starting point
    currentPath.push(startNode);
    
    //While we haven't explored all paths
    while (currentPath.size() > 0) {
      A currentToExplore = currentPath.peek();
      
      if (explored.contains(currentToExplore)) {
        currentPath.pop();
        continue;
      }
      
      //Get all nodes linked from here
      Set<B> successorsB = edges.get(currentToExplore);
      
      //We've now explored from here
      explored.add(currentToExplore);
      
      SortedSet<A> successorsA = null;
      if (successorsB != null) {
        //Convert
        successorsA = converter.convert(successorsB);

        //If we've reached a cycle
        if (successorsA.contains(startNode)) {
          return currentPath;
        }

        //Avoid exploring already explored nodes
        successorsA.removeAll(explored);
      }
      
      //If we have successor nodes to explore
      if (successorsA != null && successorsA.size() > 0) {
        //Take the first
        A first = successorsA.first();
        //Add it to our current path
        currentPath.push(first);
        
        successorsA.remove(first);
        
        //Store the alternative routes
        if (successorsA.size() > 0) {
          waitingPaths.push(successorsA);
        }
      } else {
        //Backtrack
        currentPath.pop();
        
        if (waitingPaths.size() > 0) {
          SortedSet<A> waiting = waitingPaths.peek();
          //If there's alternatives from here
          if (waiting.size() > 0) {
            //Take the first and add it to our current path
            A first = waiting.first();
            currentPath.push(first);
            waiting.remove(first);
          } else {
            waitingPaths.pop();
          }
        }
      }
    }
    
    return null;
  }*/
}
