/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.util;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.typechecker.BONST;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

public class STUtil {

  public static String getQualifiedClassString(String c, BONST st) {
    Collection<Cluster> cluster = st.classClusterMap.get(c);
    if (cluster.isEmpty()) {
      return c;
    } else {
      return getQualifiedClusterString(cluster.iterator().next().name, st) + '.' + c;
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
  
  public static String getQualifiedClusterStringForClass(Clazz c, BONST st) {
    Collection<Cluster> cluster = st.classClusterMap.get(c.name.name);
    return cluster.isEmpty() ? "" : getQualifiedClusterString(cluster.iterator().next().name, st);
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

  public static boolean isAncestor(Clazz parent, Clazz sub, BONST st) {
    //TODO more efficient search
    return getAllAncestors(sub,st).contains(parent);
  }

  public static Collection<String> getAllClassAncestors(String className, BONST st) {
    return st.simpleClassInheritanceGraph.getAllSuccessorNodes(className, Converter.<String>identityConverter());
  }
  
  public static boolean isClassAncestor(String parentName, String subName, BONST st) {
    //TODO more efficient search
    return getAllClassAncestors(subName, st).contains(parentName);
  }
  
  public static boolean isClassAncestorOrEqual(String parentName, String subName, BONST st) {
    //TODO more efficient search
    return parentName.equals(subName) || getAllClassAncestors(subName, st).contains(parentName);
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
    List<Clazz> classes = new ArrayList<Clazz>(st.classes.values());
    Collections.sort(classes, lexicographicClassComparator);
    return classes;
  }

  public static Comparator<Clazz> lexicographicClassComparator = new Comparator<Clazz>() {
    public int compare(Clazz o1, Clazz o2) {
      return o1.name.name.compareTo(o2.name.name);
    }
  };

  public static Collection<Cluster> alphabeticalClusters(final BONST st) {
    List<Cluster> clusters = new ArrayList<Cluster>(st.clusters.values());
    Collections.sort(clusters, lexicographicClusterComparator);
    return clusters;
  }

  public static Comparator<Cluster> lexicographicClusterComparator = new Comparator<Cluster>() {
    public int compare(Cluster o1, Cluster o2) {
      return o1.name.compareTo(o2.name);
    }
  };

  public static String getFeatureSignature(String name, FeatureSpecification fSpec, Clazz clazz, BONST st) {
    StringBuilder sig = new StringBuilder();
    //sig.append(getQualifiedClassString(clazz.name.name, st));
    sig.append(clazz.name.name);
    sig.append('.');
    sig.append(name);
    
    //Due to no overloading of feature names, no need for arg types in the sig
//    if (!fSpec.arguments.isEmpty()) {
//      sig.append('(');
//      List<String> argTypes = new ArrayList<String>(fSpec.arguments.size());
//      for (FeatureArgument arg : fSpec.arguments) {
//        argTypes.add(arg.type.identifier);
//      }
//      sig.append(StringUtil.appendWithSeparator(argTypes, ","));
//      sig.append(')');
//    }
    return sig.toString();
  }
  
  public static String getFeatureSignature(String name, FeatureSpecification fSpec, BONST st) {
    return getFeatureSignature(name, fSpec, st.featureDeclaringClassMap.get(fSpec), st);
  }
  
  public static Collection<KeyPair<String,FeatureSpecification>> getFeaturesForClass(Clazz clazz, BONST st) {
    return st.featuresMap.getAllPairs(clazz);
  }
}
