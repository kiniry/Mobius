package ie.ucd.bon.util;

import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.typechecker.BONST;

import java.util.Collection;
import java.util.Set;

public class STUtil {

  public static <T> Set<T> getAllSuccessorNodes(Graph<T,T> graph, T startNode, Set<T> seen) {
    Collection<T> linked = graph.get(startNode);
    for (T t : linked) {
      if (!seen.contains(t)) {
        seen.add(t);
        getAllSuccessorNodes(graph, t, seen);
      }
    }    
    return seen;
  }
  
  public static <T> Set<T> getAllPredecessorNodes(Graph<T,T> graph, T startNode, Set<T> seen) {
    Collection<T> linked = graph.reverse().get(startNode);
    for (T t : linked) {
      if (!seen.contains(t)) {
        seen.add(t);
        getAllPredecessorNodes(graph, t, seen);
      }
    }    
    return seen;
  }
  
  public static String getQualifiedClassString(String c, BONST st) {
    Cluster cluster = st.classClusterMap.get(c);
    if (cluster == null) {
      return c;
    } else {
      return getQualifiedClusterString(cluster.name, st) + '.' + c;
    }
  }
  
  public static String getQualifiedClusterString(String c, BONST st) {
    Collection<Cluster> clusters = st.clusterClusterGraph.get(c);
    if (clusters == null || clusters.size() < 1) {
      return c;
    } else {
      return getQualifiedClusterString(clusters.iterator().next().name, st) + '.' + c;
    }
  }
}
