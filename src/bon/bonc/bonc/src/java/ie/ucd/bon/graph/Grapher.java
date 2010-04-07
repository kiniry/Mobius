/**
 * Copyright (c) 2007-2010, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.graph;

import ie.ucd.bon.Main;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.BONST;
import ie.ucd.bon.util.XMLWriter;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import com.google.common.collect.Multimap;

public class Grapher {

  private static final String NEW_LINE = System.getProperty("line.separator");
  private static void appendLine(final StringBuilder sb) {
    sb.append(NEW_LINE);
  }
  private static void appendLine(final String line, final StringBuilder sb) {
    sb.append(line);
    sb.append(NEW_LINE);
  }


  public static String graphInformalClassInheritance(final ParsingTracker parseTracker) {
    Main.logDebug("Printing informal class inheritance graph");
    StringBuilder sb = new StringBuilder();

    BONST st = parseTracker.getSymbolTable();

    printGraphName(st, sb);

    printInformalClasses(st, sb);

    Graph<String,String> classInheritanceGraph = st.informal.simpleClassInheritanceGraph; 

    appendLine("//Class inheritance links", sb);
    for (String subclassName : classInheritanceGraph.keys()) {
      for (String parentClassName : classInheritanceGraph.get(subclassName)) {
        printClassInheritanceLink(subclassName, parentClassName, sb);
      }
    }
    appendLine(sb);

    appendLine("}", sb);
    return sb.toString();
  }

  private static void printGraphName(BONST st, StringBuilder sb) {
    String graphName;
    ClusterChart sysDef = st.informal.systemChart;
    if (sysDef == null) {
      graphName = "System";
    } else {
      graphName = "System: " + sysDef.getName();
    }
    appendLine("digraph \"" + graphName + "\" {", sb);
    appendLine(sb);
  }

  private static void printClassInheritanceLink(final String child, final String parent, final StringBuilder sb) {
    appendLine("\"" + parent + "\" -> \"" + child + "\";", sb);
  }

  public static String graphInformalClusterContainment(final ParsingTracker parseTracker) {
    StringBuilder sb = new StringBuilder();

    BONST st = parseTracker.getSymbolTable();

    printGraphName(st, sb);

    Graph<String,ClusterChart> classClusterGraph = st.informal.classClusterGraph;
    Graph<String,ClusterChart> clusterClusterGraph = st.informal.clusterClusterGraph;

    printInformalClasses(st, sb);
    printInformalClusters(st, sb);

    ClusterChart sysDef = st.informal.systemChart;
    if (sysDef != null) {
      String systemName = sysDef.getName();
      if (systemName != null) {
        printSystemNode(systemName, sb);
        appendLine("//Cluster-system links", sb);
        for (ClusterChart cluster : clusterClusterGraph.get(systemName)) {
          printClusterSystemLink(cluster.name, systemName, sb);
        }
        appendLine(sb);
      }
    }

    appendLine("//Cluster-cluster links", sb);
    for (String clusterName : clusterClusterGraph.keys()) {
      Collection<ClusterChart> containingClusters = clusterClusterGraph.get(clusterName);
      for (ClusterChart containingCluster : containingClusters) {
        printClusterClusterLink(clusterName, containingCluster, sb);
      }
    }
    appendLine(sb);

    appendLine("//Class-cluster links", sb);
    for (String className : classClusterGraph.keys()) {
      Collection<ClusterChart> containingClusters = classClusterGraph.get(className);
      for (ClusterChart containingCluster : containingClusters) {
        printClassClusterLink(className, containingCluster, sb);
      }
    }
    appendLine(sb);

    appendLine("}", sb);
    return sb.toString();
  }

  private static void printSystemNode(String systemName, StringBuilder sb) {
    appendLine("//System", sb);
    String comment = "System: " + systemName;
    //TODO Change shape for system?
    appendLine("\"" + systemName + "\" [shape=box,comment=\"" + comment + "\"];", sb);
    appendLine(sb);
  }

  private static void printInformalClasses(BONST st, StringBuilder sb) {
    appendLine("//Classes", sb);
    for (String className : st.informal.classes.keySet()) {
      printClass(className, sb);
    }
    appendLine(sb);
  }

  private static void printClass(final String className, final StringBuilder sb) {
    String comment = "Class: " + className;
    appendLine("\"" + className + "\" [shape=octagon,comment=\"" + comment + "\"];", sb);
  }

  private static void printInformalClusters(BONST st, StringBuilder sb) {
    Map<String, ClusterChart> clusters = st.informal.clusters;

    appendLine("//Clusters", sb);
    for (ClusterChart clusterDef : clusters.values()) {
      printCluster(clusterDef, sb);
    }
    appendLine(sb);
  }

  private static void printCluster(final ClusterChart cluster, final StringBuilder sb) {
    String comment = "Cluster: " + cluster.name;
    appendLine("\"" + cluster.name + "\" [shape=box,comment=\"" + comment + "\"];", sb);
  }

  private static void printClusterSystemLink(final String clusterName, final String systemName, final StringBuilder sb) {
    appendLine("\"" + systemName + "\" -> \"" + clusterName + "\";", sb);
  }

  private static void printClassClusterLink(final String className, final ClusterChart cluster, final StringBuilder sb) {
    appendLine("\"" + cluster.name + "\" -> \"" + className + "\";", sb);
  }

  private static void printClusterClusterLink(final String childClusterName, final ClusterChart parentCluster, final StringBuilder sb) {
    appendLine("\"" + parentCluster.name + "\" -> \"" + childClusterName + "\";", sb);
  }


  public static String graphPrefuseInformalClusterContainment(ParsingTracker parseTracker) {
    //Output
    StringWriter sw = new StringWriter();
    XMLWriter xw = new XMLWriter(sw);

    //Relevant collected data
    BONST st = parseTracker.getSymbolTable();

    try {
      //Start xml
      xw.writeEntity("tree");
      xw.writeEntity("declarations");

      xw.writeEntity("attributeDecl");
      xw.writeAttribute("name", "name");
      xw.writeAttribute("type", "String");
      xw.endEntity(); //attributeDecl

      xw.writeEntity("attributeDecl");
      xw.writeAttribute("name", "cluster");
      xw.writeAttribute("type", "Boolean");
      xw.endEntity(); //attributeDecl

      xw.writeEntity("attributeDecl");
      xw.writeAttribute("name", "class");
      xw.writeAttribute("type", "Boolean");
      xw.endEntity(); //attributeDecl

      xw.writeEntity("attributeDecl");
      xw.writeAttribute("name", "system");
      xw.writeAttribute("type", "Boolean");
      xw.endEntity(); //attributeDecl

      xw.endEntity(); //declarations

      //Top-level branch/system node
      xw.writeEntity("branch");

      ClusterChart sysDef = st.informal.systemChart;
      if (sysDef == null) {
        printPrefuseAttribute("name", "Unnamed System", xw);
      } else {
        printPrefuseAttribute("name", sysDef.name, xw);
      }

      printPrefuseAttribute("system", "true", xw);
      if (sysDef != null) {
        //TODO alphabetical order
        for (String clusterName : st.informal.clusterClusterGraph.reverse().get(sysDef)) {
          ClusterChart cluster = st.informal.clusters.get(clusterName);
          if (cluster != null) {
            printPrefuseCluster(cluster, st, xw);
          }
        }
      }

      xw.endEntity(); //system node/top-level branch

      xw.endEntity(); //tree
      xw.close();
      return sw.toString();
    } catch (IOException ioe) {
      Main.logDebug("IOException while writing XML: " + ioe);
      return "";
    }
  }

  private static void printPrefuseCluster(ClusterChart cluster, BONST st, XMLWriter xw) throws IOException {

    Multimap<ClusterChart,String> reverseClusterClusterGraph = st.informal.clusterClusterGraph.reverse();
    Multimap<ClusterChart,String> reverseClassClusterGraph = st.informal.classClusterGraph.reverse();

    Collection<String> clusters = reverseClusterClusterGraph.get(cluster);
    Collection<String> classes = reverseClassClusterGraph.get(cluster);

    if (clusters != null || classes != null) {
      xw.writeEntity("branch");

      printPrefuseAttribute("name", cluster.name, xw);
      printPrefuseAttribute("cluster", "true", xw);

      if (clusters != null) {
        clusters = new TreeSet<String>(clusters);
        for (String childClusterName : clusters) {
          ClusterChart childCluster = st.informal.clusters.get(childClusterName);
          if (childCluster != null) {
            printPrefuseCluster(childCluster, st, xw);
          }
        }
      }
      if (classes != null) {
        classes = new TreeSet<String>(classes);
        for (String childClassName : classes) {
          printPrefuseClass(childClassName, xw);
        }
      }
      xw.endEntity(); //branch
    } else {
      xw.writeEntity("leaf");
      printPrefuseAttribute("name", cluster.name, xw);
      printPrefuseAttribute("cluster", "true", xw);
      xw.endEntity(); //leaf
    }

  }

  private static void printPrefuseClass(String className, XMLWriter xw) throws IOException {
    xw.writeEntity("leaf");
    printPrefuseAttribute("name", className, xw);
    printPrefuseAttribute("class", "true", xw);
    xw.endEntity(); //leaf
  }

  private static void printPrefuseAttribute(String name, String value, XMLWriter xw) throws IOException {
    xw.writeEntity("attribute");
    xw.writeAttribute("name", name);
    xw.writeAttribute("value", value);
    xw.endEntity();
  }

  public static String graphPrefuseInformalInheritance(ParsingTracker parseTracker) {
    //Output
    StringWriter sw = new StringWriter();
    XMLWriter xw = new XMLWriter(sw);

    //Relevant collected data
    BONST st = parseTracker.getSymbolTable();
    
    //TODO alphabetical
    Set<ClassChart> topLevel = new LinkedHashSet<ClassChart>();
    for (ClassChart clazz : st.informal.classes.values()) {
      if (!st.informal.classInheritanceGraph.containsKey(clazz)) {
        topLevel.add(clazz);
      }
    }

    try {
      //Start xml
      xw.writeEntity("tree");
      xw.writeEntity("declarations");

      xw.writeEntity("attributeDecl");
      xw.writeAttribute("name", "name");
      xw.writeAttribute("type", "String");
      xw.endEntity(); //attributeDecl

      xw.writeEntity("attributeDecl");
      xw.writeAttribute("name", "class");
      xw.writeAttribute("type", "Boolean");
      xw.endEntity(); //attributeDecl

      xw.endEntity(); //declarations

      //Top-level branch/system node
      xw.writeEntity("branch");

      printPrefuseAttribute("name", "ANY", xw);

      for (ClassChart clazz : topLevel) {
        printPrefuseClassWithInheritance(clazz, st, xw);
      }

      xw.endEntity(); //system node/top-level branch

      xw.endEntity(); //tree
      xw.close();
      return sw.toString();
    } catch (IOException ioe) {
      Main.logDebug("IOException while writing XML: " + ioe);
      return "";
    }
  }

  private static void printPrefuseClassWithInheritance(ClassChart clazz, BONST st, XMLWriter xw) throws IOException {

    Multimap<String,ClassChart> reverseInheritanceGraph = st.informal.classInheritanceGraph.reverse();
    Collection<ClassChart> subclasses = reverseInheritanceGraph.get(clazz.name.name);

    if (subclasses != null && subclasses.size() > 0) {
      xw.writeEntity("branch");

      printPrefuseAttribute("name", clazz.name.name, xw);
      printPrefuseAttribute("class", "true", xw);

      for (ClassChart subclass : subclasses) {
        printPrefuseClassWithInheritance(subclass, st, xw);
      }
      xw.endEntity(); //branch
    } else {
      xw.writeEntity("leaf");
      printPrefuseAttribute("name", clazz.name.name, xw);
      printPrefuseAttribute("class", "true", xw);
      xw.endEntity(); //leaf
    }
  }


}
