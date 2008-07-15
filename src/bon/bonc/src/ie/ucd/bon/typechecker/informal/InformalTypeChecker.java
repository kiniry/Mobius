/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal;

import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.graph.Converter;
import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.Context;
import ie.ucd.bon.typechecker.errors.CycleInRelationsError;
import ie.ucd.bon.typechecker.errors.InvalidClusterTypeError;
import ie.ucd.bon.typechecker.errors.NotContainedInClusterError;
import ie.ucd.bon.typechecker.errors.SystemNotDefinedError;
import ie.ucd.bon.typechecker.informal.errors.ClassNotInAnyClusterError;
import ie.ucd.bon.typechecker.informal.errors.ClusterNotInAnyClusterOrSystemError;
import ie.ucd.bon.typechecker.informal.errors.IncorrectSystemNameError;
import ie.ucd.bon.typechecker.informal.errors.InvalidInformalClassTypeError;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

public class InformalTypeChecker {

  private final Problems problems;
  private final Context context;
  
  private final Map<String,ClusterChartDefinition> clusters;
  private final Map<String,ClassChartDefinition> classes;  
  private final SystemChartDefinition system;
  
  private final Graph<String,ClusterChartDefinition> classClusterGraph;
  private final Graph<String,ClusterChartDefinition> clusterClusterGraph;
  private final Set<String> clustersInSystem;
  
  private final Graph<String,String> classInheritanceGraph;
  
  public InformalTypeChecker(SystemChartDefinition system,
      Map<String, ClusterChartDefinition> clusters,
      Map<String, ClassChartDefinition> classes,
      Set<String> clustersInSystem,
      Graph<String, ClusterChartDefinition> clusterClusterGraph,
      Graph<String, ClusterChartDefinition> classClusterGraph,
      Graph<String,String> classInheritanceGraph) {
    this.clusters = clusters;
    this.classes = classes;
    this.system = system;
    this.classClusterGraph = classClusterGraph;
    this.clusterClusterGraph = clusterClusterGraph;
    this.clustersInSystem = clustersInSystem;
    this.classInheritanceGraph = classInheritanceGraph;
    
    this.context = Context.getContext();
    this.problems = new Problems();
  }
 
  public Problems getProblems() {
    return problems;
  }
  
  /**
   * Perform checks on the collected information from the parsing phase
   */
  public void performPreliminaryChecks() {
    //Check System defined
    if (system == null) {
      problems.addProblem(new SystemNotDefinedError());
    }
    
    //Check cyclicals
    checkClusterContainmentForCycles();
    checkClassInheritanceForCycles();
    
    //Check each class in Cluster
    checkAllClassesInClusters();
    
    //Check each cluster in another cluster or system
    checkAllClustersInClustersOrSystem();
  }
  
  public void checkClusterContainmentForCycles() {
    Converter<ClusterChartDefinition,String> converter = new Converter<ClusterChartDefinition,String>() {
      public final String convert(final ClusterChartDefinition toConvert) {
        return toConvert.getClusterName();
      }              
    };
    
    for (String clusterName : clusters.keySet()) {      
      Collection<String> cycle = clusterClusterGraph.findCycle(clusterName,converter);
      if (cycle != null) {
        ClusterChartDefinition cluster = clusters.get(clusterName);
        cluster.setHasClusterHierarchyCycle();
        problems.addProblem(new CycleInRelationsError(cluster.getSourceLocation(), "Cluster", clusterName, cycle, "clustering hierarchy"));
      }
    }
  }
  
  public void checkClassInheritanceForCycles() {
    for (String className : classes.keySet()) {
      Collection<String> cycle = classInheritanceGraph.findCycle(className, Converter.stringIdentityConverter);
      if (cycle != null) {
        ClassChartDefinition classDef = classes.get(className);
        classDef.setHasClassHierarchyCycle();
        problems.addProblem(new CycleInRelationsError(classDef.getSourceLocation(), "Class", className, cycle, "class hierarchy"));
      }
    }
  }
  
  public void checkAllClassesInClusters() {
    Set<String> allClasses = classes.keySet();
    for (String className : allClasses) {
      if (!classClusterGraph.hasEdge(className)) {
        SourceLocation loc = classes.get(className).getSourceLocation();
        problems.addProblem(new ClassNotInAnyClusterError(loc, className));
      }
    }
  }
  
  public void checkAllClustersInClustersOrSystem() {
    Set<String> allClusters = clusters.keySet();
    for (String clusterName : allClusters) {
      if (!clusterClusterGraph.hasEdge(clusterName) && !clustersInSystem.contains(clusterName)) {
        SourceLocation loc = clusters.get(clusterName).getSourceLocation();
        problems.addProblem(new ClusterNotInAnyClusterOrSystemError(loc, clusterName));
      }
    }
  }
  
  public void checkValidClassType(String className, SourceLocation loc) {
    if (!classes.containsKey(className)) {
      problems.addProblem(new InvalidInformalClassTypeError(loc, className));
    }
  }
  
  public void checkValidClusterType(String clusterName, SourceLocation loc) {
    if (!clusters.containsKey(clusterName)) {
      problems.addProblem(new InvalidClusterTypeError(loc, clusterName));
    }
  }
  
  public void checkClassIsInCluster(String className, String clusterName, SourceLocation loc) {
    Set<ClusterChartDefinition> inClusters = classClusterGraph.getLinkedNodes(className);
    ClusterChartDefinition cluster = clusters.get(clusterName);
    if (cluster != null) {
      if (inClusters == null || !inClusters.contains(cluster)) {
        problems.addProblem(new NotContainedInClusterError(loc, className, true, clusterName));
      }
    }
  }
  
  public void checkSystemName(String systemName, SourceLocation loc) {
    if (system != null && !system.getSystemName().equals(systemName)) {
      problems.addProblem(new IncorrectSystemNameError(loc, systemName, system.getSystemName(), 
          system.getSourceLocation().getSourceFilePath(), system.getSourceLocation().getLineNumber()));
    }
  }
  
  
  public void checkValidClassTypeByContext(String className, SourceLocation loc) {
    if (context.isInInheritsClause()) {
      checkValidClassType(className, loc);
    } else if (context.isInEventEntry()) {
      checkValidClassType(className, loc);
    } else if (context.isInCreationEntry()) {
      checkValidClassType(className, loc);
    } 
  }
  
  public void checkValidClusterTypeByContext(String clusterName, SourceLocation loc) {
    if (context.isInDictionaryEntry()) {
      checkValidClusterType(clusterName, loc);
      String className = context.getDictionaryEntryClassName();
      loc.setStartToken(context.getDictionaryEntryStartToken());
      checkClassIsInCluster(className, clusterName, loc);
    }
  }
  
}
