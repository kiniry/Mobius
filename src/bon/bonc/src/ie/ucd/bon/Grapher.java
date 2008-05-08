/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.ClassDefinition;
import ie.ucd.bon.typechecker.ClusterDefinition;
import ie.ucd.bon.typechecker.TypingInformation;
import ie.ucd.bon.util.FileUtil;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.Map;

public class Grapher {


  public static void graphClassesAndClusters(final ParsingTracker parseTracker, final String fileToPrintTo) {
    File file = new File(fileToPrintTo);
    File dir = file.getParentFile();
    if (!FileUtil.checkDirExists(dir)) {
      System.out.println("Error, unable to create directory: " + dir);
      return;
    }
    
    System.out.println("Creating graph: " + fileToPrintTo);
    try {
      PrintWriter printer = new PrintWriter(fileToPrintTo);

      TypingInformation typingInfo = parseTracker.getTypingInformation();

      Map<String, ClusterDefinition> clusters = typingInfo.getClusters();
      Map<String, ClassDefinition> classes = typingInfo.getClasses();
      //Map<String, ClusterDefinition> clusterClusterLinks = typingInfo.getClusterClusterContainsLink();
      //Map<String, ClusterDefinition> classClusterLinks = typingInfo.getClassClusterContainsLink();

      String graphName;
      if (typingInfo.informal().getSystem() == null) {
        graphName = "System";
      } else {        
        graphName = "System: " + typingInfo.informal().getSystem().getSystemName();
      }
      printer.println("digraph \"" + graphName + "\" {");
      printer.println();
      
      //Print Clusters
      printer.println("//Clusters");
      for (ClusterDefinition cluster : clusters.values()) {
        printCluster(cluster, printer);
      }
      printer.println();
      
      //Print Classes
      printer.println("//Classes");
      for (ClassDefinition classDef : classes.values()) {
        printClass(classDef, printer);
      }
      printer.println();
      
      //Print Cluster-Cluster links
//      printer.println("//Cluster-Cluster links");
//      for (Map.Entry<String, ClusterDefinition> entry : clusterClusterLinks.entrySet()) {
//        String name = entry.getKey();
//        ClusterDefinition containingCluster = entry.getValue();
//        printClusterClusterLink(clusters.get(name),containingCluster, printer);
//      }
//      printer.println();
      
      //Print Cluster-Cluster links
//      printer.println("//Class-Cluster links");
//      for (Map.Entry<String,ClusterDefinition> entry : classClusterLinks.entrySet()) {
//        String name = entry.getKey();
//        ClusterDefinition containingCluster = entry.getValue();
//        printClassClusterLink(classes.get(name),containingCluster, printer);
//      }
//      printer.println();
      
      printer.println("}");
      printer.println();
      printer.close();
    } catch (FileNotFoundException fnfe) {
      System.out.println("ERROR: Unable to create or write to file " + fileToPrintTo);
    }
  }

  private static void printCluster(final ClusterDefinition cluster, final PrintWriter printer) {
    String comment = "Cluster: " + cluster.getClusterName();
    printer.println("\"" + cluster.getClusterName() + "\" [shape=box,comment=\"" + comment + "\"];");
  }
  
  private static void printClass(final ClassDefinition classDef, final PrintWriter printer) {
    String comment = "Class: " + classDef.getClassName();
    printer.println("\"" + classDef.getClassName() + "\" [shape=octagon,comment=\"" + comment + "\"];");
  }
  
  private static void printClassClusterLink(final ClassDefinition classDef, final ClusterDefinition cluster, final PrintWriter printer) {
    printer.println("\"" + cluster.getClusterName() + "\" -> \"" + classDef.getClassName() + "\";");
  }
  
  private static void printClusterClusterLink(final ClusterDefinition childCluster, final ClusterDefinition parentCluster, final PrintWriter printer) {
    printer.println("\"" + parentCluster.getClusterName() + "\" -> \"" + childCluster.getClusterName() + "\";");
  }

  private static void printClassInheritenceLink(final String child, final String parent, final PrintWriter printer) {
    printer.println("\"" + parent + "\" -> \"" + child + "\";");
  }
  
  public static void graphClassHierarchy(final ParsingTracker parseTracker, final String fileToPrintTo) {
    File file = new File(fileToPrintTo);
    File dir = file.getParentFile();
    if (!FileUtil.checkDirExists(dir)) {
      System.out.println("Error, unable to create directory: " + dir);
      return;
    }
    
    System.out.println("Creating graph: " + fileToPrintTo);
    try {
      PrintWriter printer = new PrintWriter(fileToPrintTo);

      TypingInformation typingInfo = parseTracker.getTypingInformation();

      Map<String, ClassDefinition> classes = typingInfo.getClasses();
      //Map<String, Set<String>> inherits = typingInfo.getInherits();
      
      String graphName;
      if (typingInfo.informal().getSystem() == null) {
        graphName = "System";
      } else {
        graphName = "System: " + typingInfo.informal().getSystem().getSystemName();
      }
      printer.println("digraph \"" + graphName + "\" {");
      printer.println();
      
      //Print Classes
      printer.println("//Classes");
      for (ClassDefinition classDef : classes.values()) {
        printClass(classDef, printer);
      }
      printer.println();
      
      //Print Inherits
      /*printer.println("//Inherits");
      for (Map.Entry<String,Set<String>> entry : inherits.entrySet()) {
        String child = entry.getKey(); 
        Set<String> parents = entry.getValue();
        
        for (String parent : parents) {
          printClassInheritenceLink(child, parent, printer);
        }
      }*/
      
      printer.println("}");
      printer.println();
      printer.close();
    } catch (FileNotFoundException fnfe) {
      System.out.println("ERROR: Unable to create or write to file " + fileToPrintTo);
    }
  }
  
}
