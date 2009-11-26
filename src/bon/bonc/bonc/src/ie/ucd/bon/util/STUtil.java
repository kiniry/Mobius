package ie.ucd.bon.util;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.typechecker.BONST;

import java.util.Collection;
import java.util.Comparator;
import java.util.TreeSet;

public class STUtil {

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
  
  public static Collection<Clazz> getAllDescendants(Clazz clazz, BONST st) {
    return classNameToClazzConverter(st).convert(st.simpleClassInheritanceGraph.getAllPredecessorNodes(clazz.name.name, Converter.<String>identityConverter()));
  }
  
  public static Collection<Clazz> getImmediateDescendants(Clazz clazz, BONST st) {
    return classNameToClazzConverter(st).convert(st.simpleClassInheritanceGraph.reverse().get(clazz.name.name));
  }
  
  public static Collection<Clazz> getAllAncestors(Clazz clazz, BONST st) {
    return classNameToClazzConverter(st).convert(st.simpleClassInheritanceGraph.getAllSuccessorNodes(clazz.name.name, Converter.<String>identityConverter()));
  }
  
  public static Collection<Clazz> getImmediateAncestors(Clazz clazz, BONST st) {
    return classNameToClazzConverter(st).convert(st.simpleClassInheritanceGraph.get(clazz.name.name));
  }
  
  public static Converter<String,Clazz> classNameToClazzConverter(final BONST st) {
    return new Converter<String,Clazz>() {      
      @Override
      public Clazz convert(String toConvert) {
        return st.classes.get(toConvert);
      }
    };
  }
  
  public static Collection<Clazz> alphabeticalClasses(final BONST st) {
    Collection<Clazz> classes = new TreeSet<Clazz>(lexicographicClassComparator);
    classes.addAll(st.classes.values());
    return classes;
  }
  
  public static Comparator<Clazz> lexicographicClassComparator = new Comparator<Clazz>() {
    @Override
    public int compare(Clazz o1, Clazz o2) {
      return o1.name.name.compareTo(o2.name.name);
    }
  };
  
  public static Collection<Cluster> alphabeticalClusters(final BONST st) {
    Collection<Cluster> clusters = new TreeSet<Cluster>(lexicographicClusterComparator);
    clusters.addAll(st.clusters.values());
    return clusters;
  }
  
  public static Comparator<Cluster> lexicographicClusterComparator = new Comparator<Cluster>() {
    @Override
    public int compare(Cluster o1, Cluster o2) {
      return o1.name.compareTo(o2.name);
    }
  };
}
