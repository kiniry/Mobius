package ie.ucd.bon.typechecker;

import ie.ucd.bon.Main;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.graph.Converter;
import ie.ucd.bon.typechecker.errors.CycleInRelationsError;
import ie.ucd.bon.typechecker.informal.errors.ClassNotInAnyClusterError;
import ie.ucd.bon.typechecker.informal.errors.ClusterNotInAnyClusterOrSystemError;
import ie.ucd.bon.typechecker.informal.errors.SystemNotDefinedError;

import java.util.Collection;
import java.util.Set;

public class PreliminaryChecker {

  private final Problems problems;
  private final BONST st;
  
  public PreliminaryChecker(BONST st) {
    problems = new Problems("Prelim");
    this.st = st;
  }

  public Problems getProblems() {
    return problems;
  }
  
  public void runChecks(boolean checkFormal, boolean checkInformal) {
    if (checkFormal) {
      checkFormalGraphsForCycles();
    }
    
    if (checkInformal) {
      checkInformalGraphsForCycles();
      checkSystemDefined();
      checkAllClassesInClusters();
      checkAllClustersInClustersOrSystem();
    }
  }
  
  public void checkInformalGraphsForCycles() {
    Main.logDebug("Check informal class inheritance for cycles");
    for (ClassChart classChart : st.informal.classes.values()) {
      Collection<ClassChart> cycle = 
        st.informal.classInheritanceGraph.findCycle(classChart, 
          new Converter<String,ClassChart>() {
            public ClassChart convert(final String name) {
               return st.informal.classes.get(name);
            }
          });
      if (cycle != null) {
        //TODO mark class as having cycle
        problems.addProblem(new CycleInRelationsError(classChart.getLocation(), "Class", classChart, cycle, "class hierarchy"));
      }
    }
    
    Main.logDebug("Checking informal clusters for cycles");
    for (ClusterChart clusterChart : st.informal.clusters.values()) { 
      Collection<String> cycle = 
        st.informal.clusterClusterGraph.findCycle(clusterChart.getName(),
          new Converter<ClusterChart,String>() {
            public String convert(final ClusterChart name) {
              return name.getName();
            }
          });
      if (cycle != null) {
        //TODO mark cluster as having cycle
        problems.addProblem(new CycleInRelationsError(clusterChart.getLocation(), "Cluster", clusterChart, cycle, "clustering hierarchy"));
      }
    }
  }

  public void checkFormalGraphsForCycles() {
    
  }

  public void checkAllClassesInClusters() {
    Set<String> allClassNames = st.informal.classes.keySet();
    for (String className : allClassNames) {
      if (!st.informal.classClusterGraph.containsKey(className)) {
        ClassChart clazz = st.informal.classes.get(className);
        problems.addProblem(new ClassNotInAnyClusterError(clazz.getLocation(), className));
      }
    }
  }
  
  public void checkAllClustersInClustersOrSystem() {
    Set<String> allClusterNames = st.informal.clusters.keySet();
    for (String clusterName : allClusterNames) {
      if (!st.informal.clusterClusterGraph.containsKey(clusterName)) {
        ClusterChart cluster = st.informal.clusters.get(clusterName);
        if (!cluster.getIsSystem()) {
          problems.addProblem(new ClusterNotInAnyClusterOrSystemError(cluster.getLocation(), clusterName));
        }
      }
    }
  }

  public void checkSystemDefined() {
    if (st.informal.systemChart == null) {
      problems.addProblem(new SystemNotDefinedError());
    }
  }
  
}
