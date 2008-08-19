/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal;

import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.Context;
import ie.ucd.bon.typechecker.errors.ClassCannotHaveSelfAsParentError;
import ie.ucd.bon.typechecker.errors.DuplicateSuperclassWarning;
import ie.ucd.bon.typechecker.errors.DuplicateSystemDefinitionError;
import ie.ucd.bon.typechecker.informal.errors.DuplicateClassChartError;
import ie.ucd.bon.typechecker.informal.errors.DuplicateClusterChartError;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

public class InformalTypingInformation {
  
  private final Problems problems;
  private final Context context;
  
  private final Map<String,ClusterChartDefinition> clusters;
  private final Map<String,ClassChartDefinition> classes;  
  private SystemChartDefinition system;
  
  private final Graph<String,ClusterChartDefinition> classClusterGraph;
  private final Graph<String,ClusterChartDefinition> clusterClusterGraph;
  private final Set<String> clustersInSystem;
  
  private final Graph<String,String> classInheritanceGraph;
  
  private final Graph<String,String> alternativeClassDescriptionsGraph;
    
  public InformalTypingInformation(Context context) {
    this.context = context;
    
    clusters = new HashMap<String,ClusterChartDefinition>();
    classes = new HashMap<String,ClassChartDefinition>();
    
    classClusterGraph = new Graph<String,ClusterChartDefinition>();
    clusterClusterGraph = new Graph<String,ClusterChartDefinition>();
    clustersInSystem = new HashSet<String>();
    
    classInheritanceGraph = new Graph<String,String>();
    
    alternativeClassDescriptionsGraph = new Graph<String,String>();
    
    problems = new Problems();
  }
  
  public void setSystem(String systemName, SourceLocation loc) {
    if (this.system == null) {
      system = new SystemChartDefinition(systemName, loc);
    } else {
      problems.addProblem(new DuplicateSystemDefinitionError(loc, system));
    }
  }

  /**
   * Adds a cluster name to the typing information.
   * @param clusterName The name of the cluster to add.
   */
  public void addCluster(String clusterName, SourceLocation loc) {
    ClusterChartDefinition cluster = clusters.get(clusterName);
    if (cluster != null) {
      problems.addProblem(new DuplicateClusterChartError(loc, cluster));
      return;
    }
    cluster = new ClusterChartDefinition(clusterName, loc);
    clusters.put(clusterName, cluster);
  }
  
  /**
   * Adds a class name to the typing information.
   * @param className The name of the class to add.
   */
  public void addClass(String className, SourceLocation loc) {
    ClassChartDefinition classDef = classes.get(className);
    if (classDef != null) {
      problems.addProblem(new DuplicateClassChartError(loc, classDef));
      return;
    }
    classDef = new ClassChartDefinition(className, loc);
    classes.put(className, classDef);
  }
  
  public void addQuery(String query) {
    if (context.isInClassChart()) {
      ClassChartDefinition def = classes.get(context.getClassChartName());
      if (def != null) {
        def.addQuery(query);
      }
    }
  }
  
  public void addCommand(String command) {
    if (context.isInClassChart()) {
      ClassChartDefinition def = classes.get(context.getClassChartName());
      if (def != null) {
        def.addCommand(command);
      }
    }
  }
  
  public void addConstraint(String constraint) {
    if (context.isInClassChart()) {
      ClassChartDefinition def = classes.get(context.getClassChartName());
      if (def != null) {
        def.addConstraint(constraint);
      }
    }
  }

  
  public void addClusterEntry(String clusterName) {
    if (context.isInSystemChart()) {
      clustersInSystem.add(clusterName);
    } else if (context.isInClusterChart()) {
      clusterClusterGraph.addEdge(clusterName, clusters.get(context.getClusterChartName()));
    }
  }
  
  public void addClassEntry(String className) {
    if (context.isInClusterChart()) {
      //Should be, sanity check anyway
      classClusterGraph.addEdge(className, clusters.get(context.getClusterChartName()));
    }
  }
  
  public void classNameListEntry(String className, SourceLocation loc) {
    if (context.isInInheritsClause()) {
      addParentClass(className, loc);
    }
  }
  
  public void addParentClass(String className, SourceLocation loc) {
    //System.out.println("Adding informal parent class: " + className);
    String currentClassName = context.getClassChartName();
    if (context.getClassChartName().equals(className)) {
      problems.addProblem(new ClassCannotHaveSelfAsParentError(loc, currentClassName));
    } else {
      
      if (classInheritanceGraph.hasEdge(currentClassName, className)) {
        problems.addProblem(new DuplicateSuperclassWarning(loc,context.getClassChartName(),className));
      } else {
        classInheritanceGraph.addEdge(currentClassName, className);
        ClassChartDefinition classDef = classes.get(currentClassName);
        classDef.addSuperClass(className);
      }

    }   
  }
  
  public void setExplanation(String explanation) {
    if (context.isInClassChart()) {
      String name = context.getClassChartName();
      classes.get(name).setExplanation(explanation);
    }
  }
  
  public SystemChartDefinition getSystem() {
    return system;
  }

  public Problems getProblems() {
    return problems;
  }
  
  public Map<String, ClusterChartDefinition> getClusters() {
    return clusters;
  }

  public Map<String, ClassChartDefinition> getClasses() {
    return classes;
  }

  public InformalTypeChecker getInformalTypeChecker() {
    return new InformalTypeChecker(system, clusters, classes, clustersInSystem, clusterClusterGraph, classClusterGraph, classInheritanceGraph);
  }

  public Graph<String, ClusterChartDefinition> getClassClusterGraph() {
    return classClusterGraph;
  }
  
  public Graph<String, ClusterChartDefinition> getClusterClusterGraph() {
    return clusterClusterGraph;
  }

  public Set<String> getClustersInSystem() {
    return clustersInSystem;
  }

  public Graph<String, String> getClassInheritanceGraph() {
    return classInheritanceGraph;
  }

  public String getAlternativeClassDescription(final String className) {
    //Probably makes more sense to only store one in the first place since we'll only use one.
    //This won't make a big difference in practice, as almost always a class will be in one cluster only.
    Iterator<String> descriptions = alternativeClassDescriptionsGraph.getLinkedNodes(className).iterator();
    if (descriptions.hasNext()) {
      return descriptions.next();
    } else {
      return "";
    }    
  }
  
  public void setDescription(String description) {
    if (context.isInClassEntry()) {
      alternativeClassDescriptionsGraph.addEdge(context.getClassEntryName(), description);
    }
  }

}
