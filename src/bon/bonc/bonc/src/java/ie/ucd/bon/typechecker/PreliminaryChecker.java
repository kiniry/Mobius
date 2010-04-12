/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.Main;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.typechecker.errors.CycleInRelationsError;
import ie.ucd.bon.typechecker.informal.errors.ClassNotInAnyClusterError;
import ie.ucd.bon.typechecker.informal.errors.ClusterNotInAnyClusterOrSystemError;
import ie.ucd.bon.typechecker.informal.errors.SystemNotDefinedError;
import ie.ucd.bon.util.AstUtil;
import ie.ucd.bon.util.Converter;

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
      Collection<ClassChart> cycle = st.informal.classInheritanceGraph.findCycle(classChart,
          new Converter<String,ClassChart>() {
            public ClassChart convert(final String name) {
              return st.informal.classes.get(name);
            }
          });
      if (cycle != null) {
        //TODO mark class as having cycle
        problems.addProblem(new CycleInRelationsError(classChart.getReportingLocation(), "Class", classChart, cycle, "class hierarchy"));
      }
    }

    Main.logDebug("Checking informal clusters for cycles");
    for (ClusterChart clusterChart : st.informal.clusters.values()) {
      Collection<String> cycle = st.informal.clusterClusterGraph.findCycle(clusterChart.getName(),
          new Converter<ClusterChart,String>() {
            public String convert(final ClusterChart name) {
              return name.getName();
            }
          });
      if (cycle != null) {
        //TODO mark cluster as having cycle
        problems.addProblem(new CycleInRelationsError(clusterChart.getReportingLocation(), "Cluster", clusterChart, cycle, "clustering hierarchy"));
      }
    }
  }

  public void checkFormalGraphsForCycles() {
    Main.logDebug("Check formal class inheritance for cycles");
    for (Clazz clazz : st.classes.values()) {
      Collection<String> cycle = st.classInheritanceGraph.findCycle(clazz.getName().getName(),
          new Converter<Type,String>() {
            public String convert(final Type type) {
              return type.getIdentifier();
            }
          });
      if (cycle != null) {
        //TODO mark class as having cycle
        problems.addProblem(new CycleInRelationsError(clazz.getReportingLocation(), "Class", clazz.getName().getName(), cycle, "class hierarchy"));
      }
    }

    Main.logDebug("Checking formal clusters for cycles");
    for (Cluster cluster : st.clusters.values()) {
      Collection<String> cycle = st.clusterClusterGraph.findCycle(cluster.getName(),
          new Converter<Cluster,String>() {
            public String convert(final Cluster name) {
              return name.getName();
            }
          });
      if (cycle != null) {
        //TODO mark cluster as having cycle
        problems.addProblem(new CycleInRelationsError(cluster.getReportingLocation(), "Cluster", cluster.getName(), cycle, "clustering hierarchy"));
      }
    }
  }

  public void checkAllClassesInClusters() {
    Set<String> allClassNames = st.informal.classes.keySet();
    for (String className : allClassNames) {
      if (!st.informal.classClusterGraph.containsKey(className)) {
        ClassChart clazz = st.informal.classes.get(className);
        problems.addProblem(new ClassNotInAnyClusterError(clazz.getReportingLocation(), className));
      }
    }
  }

  public void checkAllClustersInClustersOrSystem() {
    Set<String> allClusterNames = st.informal.clusters.keySet();
    for (String clusterName : allClusterNames) {
      if (!st.informal.clusterClusterGraph.containsKey(clusterName)) {
        ClusterChart cluster = st.informal.clusters.get(clusterName);
        if (!cluster.getIsSystem() && !AstUtil.isBuiltin(cluster)) { //TODO instead filter all issues that are from builtin source?
          problems.addProblem(new ClusterNotInAnyClusterOrSystemError(cluster.getReportingLocation(), clusterName));
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
