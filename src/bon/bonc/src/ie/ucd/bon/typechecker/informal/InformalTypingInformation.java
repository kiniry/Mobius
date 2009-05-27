/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker.informal;

import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.Context;
import ie.ucd.bon.typechecker.errors.ClassCannotHaveSelfAsParentError;
import ie.ucd.bon.typechecker.errors.DuplicateSuperclassWarning;
import ie.ucd.bon.typechecker.errors.DuplicateSystemDefinitionError;
import ie.ucd.bon.typechecker.errors.NameNotUniqueError;
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
  private ClusterChartDefinition system;
  
  private final Graph<String,ClusterChartDefinition> classClusterGraph;
  private final Graph<String,String> reverseClassClusterGraph;
  private final Graph<String,ClusterChartDefinition> clusterClusterGraph;
  private final Graph<String,String> reverseClusterClusterGraph;
  private final Set<String> clustersInSystem;
  
  private final Graph<String,String> classInheritanceGraph;
  private final Graph<String,String> reverseClassInheritanceGraph;
  
  private final Graph<String,String> alternativeClassDescriptionsGraph;
    
  public InformalTypingInformation(Context context) {
    this.context = context;
    
    clusters = new HashMap<String,ClusterChartDefinition>();
    classes = new HashMap<String,ClassChartDefinition>();
    
    classClusterGraph = new Graph<String,ClusterChartDefinition>();
    clusterClusterGraph = new Graph<String,ClusterChartDefinition>();
    reverseClassClusterGraph = new Graph<String,String>();
    reverseClusterClusterGraph = new Graph<String,String>();
    
    clustersInSystem = new HashSet<String>();
    
    classInheritanceGraph = new Graph<String,String>();
    reverseClassInheritanceGraph = new Graph<String,String>();
    
    alternativeClassDescriptionsGraph = new Graph<String,String>();
    
    problems = new Problems();
  }
  
  public void setSystem(ClusterChartDefinition newSystem) {
    if (this.system == null) {
      system = newSystem;
    } else {
      problems.addProblem(new DuplicateSystemDefinitionError(newSystem.getSourceLocation(), system));
    }
  }

  /**
   * Adds a cluster name to the typing information.
   * @param clusterName The name of the cluster to add.
   */
  public void addCluster(ClusterChartDefinition clusterDef) {
    ClassChartDefinition classDef = classes.get(clusterDef.getName());
    if (classDef != null) {
      problems.addProblem(new NameNotUniqueError(clusterDef.getSourceLocation(), "Cluster", clusterDef.getName(), "class", classDef.getSourceLocation()));
    }
    ClusterChartDefinition cluster = clusters.get(clusterDef.getName());
    if (cluster != null) {
      problems.addProblem(new DuplicateClusterChartError(clusterDef.getSourceLocation(), cluster));
    } else {
      clusters.put(clusterDef.getName(), clusterDef);
    }
  }
  
  /**
   * Adds a class name to the typing information.
   * @param className The name of the class to add.
   */
  public void addClass(ClassChartDefinition classX) {
    String className = classX.getName();
    SourceLocation loc = classX.getSourceLocation();
    ClusterChartDefinition clusterDef = clusters.get(className);
    if (clusterDef != null) {
      problems.addProblem(new NameNotUniqueError(loc, "Class chart", className, "cluster chart", clusterDef.getSourceLocation()));
    }
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
      ClassChartDefinition def = classes.get(context.getClassChart());
      if (def != null) {
        def.addQuery(query);
      }
    }
  }
  
  public void addCommand(String command) {
    if (context.isInClassChart()) {
      ClassChartDefinition def = classes.get(context.getClassChart());
      if (def != null) {
        def.addCommand(command);
      }
    }
  }
  
  public void addConstraint(String constraint) {
    if (context.isInClassChart()) {
      ClassChartDefinition def = classes.get(context.getClassChart());
      if (def != null) {
        def.addConstraint(constraint);
      }
    }
  }

  
  public void addClusterEntry(String clusterName) {
    if (context.isInSystemChart()) {
      clustersInSystem.add(clusterName);
    } else if (context.isInClusterChart()) {
      clusterClusterGraph.addEdge(clusterName, context.getClusterChart());
      reverseClusterClusterGraph.addEdge(context.getClusterChart().getName(), clusterName);
    }
  }
  
  public void addClassEntry(String className) {
    if (context.isInClusterChart()) {
      //Should be, sanity check anyway
      classClusterGraph.addEdge(className, clusters.get(context.getClusterChart()));
      reverseClassClusterGraph.addEdge(context.getClusterChart().getName(), className);
    }
  }
  
  public void classNameListEntry(String className, SourceLocation loc) {
    if (context.isInInheritsClause()) {
      addParentClass(className, loc);
    }
  }
  
  public void addParentClass(String className, SourceLocation loc) {
    //System.out.println("Adding informal parent class: " + className);
    ClassChartDefinition currentClass= context.getClassChart();
    if (context.getClassChart().getName().equals(className)) {
      problems.addProblem(new ClassCannotHaveSelfAsParentError(loc, currentClass.getName()));
    } else {
      
      if (classInheritanceGraph.hasEdge(currentClass.getName(), className)) {
        problems.addProblem(new DuplicateSuperclassWarning(loc,context.getClassChart().getName(),className));
      } else {
        classInheritanceGraph.addEdge(currentClass.getName(), className);
        reverseClassInheritanceGraph.addEdge(className, currentClass.getName());
        ClassChartDefinition classDef = classes.get(currentClass.getName());
        classDef.addSuperClass(className);
      }

    }   
  }
  
  public void setExplanation(String explanation) {
    if (context.isInClassChart()) {
      context.getClassChart().setExplanation(explanation);
    }
  }
  
  public ClusterChartDefinition getSystem() {
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

  public Graph<String, String> getReverseClassInheritanceGraph() {
    return reverseClassInheritanceGraph;
  }

  public Graph<String, String> getReverseClassClusterGraph() {
    return reverseClassClusterGraph;
  }

  public Graph<String, String> getReverseClusterClusterGraph() {
    return reverseClusterClusterGraph;
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
  
  public void indexing(Indexing indexing) {
    if (context.isInSystemChart()) {
      system.setIndexing(indexing);
    } else if (context.isInClassChart()) {
      context.getClassChart().setIndexing(indexing);
    } else if (context.isInClusterChart()) {
      context.getClusterChart().setIndexing(indexing);
    }
  }

}
