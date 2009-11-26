package ie.ucd.bon.util;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.typechecker.BONST;

import java.util.Collection;

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
}
