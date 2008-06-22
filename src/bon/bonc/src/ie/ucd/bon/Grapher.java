/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.informal.ClassChartDefinition;
import ie.ucd.bon.typechecker.informal.ClusterChartDefinition;
import ie.ucd.bon.typechecker.informal.InformalTypingInformation;
import ie.ucd.bon.typechecker.informal.SystemChartDefinition;

import java.util.Map;
import java.util.Set;

public class Grapher {

  private static String NEW_LINE = System.getProperty("line.separator");
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

    InformalTypingInformation informalTypingInfo = parseTracker.getInformalTypingInformation();

    printGraphName(informalTypingInfo, sb);

    Graph<String,String> classInheritanceGraph = informalTypingInfo.getClassInheritanceGraph();
    
    printInformalClasses(informalTypingInfo, sb);

    appendLine("//Class inheritance links", sb);
    for (String subclassName : classInheritanceGraph.getStartingNodes()) {
      for (String parentClassName : classInheritanceGraph.getLinkedNodes(subclassName)) {
        printClassInheritanceLink(subclassName, parentClassName, sb);
      }
    }    
    appendLine(sb);

    appendLine("}", sb);
    return sb.toString();
  }

  public static String graphInformalClusterContainment(final ParsingTracker parseTracker) {
    StringBuilder sb = new StringBuilder();

    InformalTypingInformation informalTypingInfo = parseTracker.getInformalTypingInformation();

    printGraphName(informalTypingInfo, sb);

    Graph<String,ClusterChartDefinition> classClusterGraph = informalTypingInfo.getClassClusterGraph();
    Graph<String,ClusterChartDefinition> clusterClusterGraph = informalTypingInfo.getClusterClusterGraph();
    Set<String> clustersInSystem = informalTypingInfo.getClustersInSystem();

    printInformalClasses(informalTypingInfo, sb);
    printInformalClusters(informalTypingInfo, sb);

    SystemChartDefinition sysDef = informalTypingInfo.getSystem();
    if (sysDef != null) {
      String systemName = sysDef.getSystemName();
      if (systemName != null) {
        printSystemNode(systemName, sb);
        appendLine("//Cluster-system links", sb);
        for (String clusterName : clustersInSystem) {
          printClusterSystemLink(clusterName, systemName, sb);
        }
        appendLine(sb);
      }
    }

    appendLine("//Cluster-cluster links", sb);
    for (String clusterName : clusterClusterGraph.getStartingNodes()) {
      Set<ClusterChartDefinition> containingClusters = clusterClusterGraph.getLinkedNodes(clusterName);
      for (ClusterChartDefinition containingCluster : containingClusters) {
        printClusterClusterLink(clusterName, containingCluster, sb);
      }
    }
    appendLine(sb);

    appendLine("//Class-cluster links", sb);
    for (String className : classClusterGraph.getStartingNodes()) {
      Set<ClusterChartDefinition> containingClusters = classClusterGraph.getLinkedNodes(className);
      for (ClusterChartDefinition containingCluster : containingClusters) {
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

  private static void printInformalClasses(InformalTypingInformation informalTypingInfo, StringBuilder sb) {
    Map<String, ClassChartDefinition> classes = informalTypingInfo.getClasses();

    appendLine("//Classes", sb);
    for (ClassChartDefinition classDef : classes.values()) {
      printClass(classDef, sb);
    }
    appendLine(sb);
  }

  private static void printInformalClusters(InformalTypingInformation informalTypingInfo, StringBuilder sb) {
    Map<String, ClusterChartDefinition> clusters = informalTypingInfo.getClusters();

    appendLine("//Clusters", sb);
    for (ClusterChartDefinition clusterDef : clusters.values()) {
      printCluster(clusterDef, sb);
    }
    appendLine(sb);
  }

  private static void printCluster(final ClusterChartDefinition cluster, final StringBuilder sb) {
    String comment = "Cluster: " + cluster.getClusterName();
    appendLine("\"" + cluster.getClusterName() + "\" [shape=box,comment=\"" + comment + "\"];", sb);
  }

  private static void printClass(final ClassChartDefinition classDef, final StringBuilder sb) {
    String comment = "Class: " + classDef.getClassName();
    appendLine("\"" + classDef.getClassName() + "\" [shape=octagon,comment=\"" + comment + "\"];", sb);
  }

  private static void printClassClusterLink(final String className, final ClusterChartDefinition cluster, final StringBuilder sb) {
    appendLine("\"" + cluster.getClusterName() + "\" -> \"" + className + "\";", sb);
  }

  private static void printClusterClusterLink(final String childClusterName, final ClusterChartDefinition parentCluster, final StringBuilder sb) {
    appendLine("\"" + parentCluster.getClusterName() + "\" -> \"" + childClusterName + "\";", sb);
  }

  private static void printClusterSystemLink(final String clusterName, final String systemName, final StringBuilder sb) {
    appendLine("\"" + systemName + "\" -> \"" + clusterName + "\";", sb);
  }
  
  private static void printClassInheritanceLink(final String child, final String parent, final StringBuilder sb) {
    appendLine("\"" + parent + "\" -> \"" + child + "\";", sb);
  }

  private static void printGraphName(InformalTypingInformation iti, StringBuilder sb) {
    String graphName;
    SystemChartDefinition sysDef = iti.getSystem();
    if (sysDef == null) {
      graphName = "System";
    } else {        
      graphName = "System: " + sysDef.getSystemName();
    }
    appendLine("digraph \"" + graphName + "\" {", sb);
    appendLine(sb);
  }

}
