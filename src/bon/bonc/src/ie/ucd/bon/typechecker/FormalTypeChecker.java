/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.Main;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.graph.Converter;
import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.errors.ClassDoesNotDeclareFeatureError;
import ie.ucd.bon.typechecker.errors.ClassIsNotGenericError;
import ie.ucd.bon.typechecker.errors.CycleInRelationsError;
import ie.ucd.bon.typechecker.errors.EffectiveClassDoesNotDefineDeferredFeatureError;
import ie.ucd.bon.typechecker.errors.InvalidFormalClassTypeError;
import ie.ucd.bon.typechecker.errors.InvalidClusterTypeError;
import ie.ucd.bon.typechecker.errors.InvalidStaticComponentTypeError;
import ie.ucd.bon.typechecker.errors.NotContainedInClusterError;
import ie.ucd.bon.typechecker.errors.TypeMismatch;
import ie.ucd.bon.typechecker.informal.ClassChartDefinition;
import ie.ucd.bon.typechecker.informal.ClassInheritanceInconsistencyError;
import ie.ucd.bon.typechecker.informal.ClassOrClusterInconsistencyError;
import ie.ucd.bon.typechecker.informal.ClusterChartDefinition;
import ie.ucd.bon.typechecker.informal.InformalTypingInformation;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.Stack;
import java.util.TreeSet;

public class FormalTypeChecker {

  private final Problems problems;
  private final Problems consistencyProblems;
  
  private final Context context;
  
  private final Map<String,ClusterDefinition> clusters;
  private final Map<String,ClassDefinition> classes;
  private final Map<String,Type> types;
  
  private final Graph<String,Type> classInheritanceGraph;
  private final Graph<String,String> simpleClassInheritanceGraph; //Non-generic 
  
  private final Graph<String,ClusterDefinition> classClusterGraph;
  private final Graph<String,ClusterDefinition> clusterClusterGraph;
  
  public FormalTypeChecker(Map<String, ClusterDefinition> clusters,
      Map<String, ClassDefinition> classes, 
      Map<String, Type> types,
      Graph<String,Type> classInheritanceGraph,
      Graph<String,String> simpleClassInheritanceGraph,
      Graph<String,ClusterDefinition> classClusterGraph,
      Graph<String,ClusterDefinition> clusterClusterGraph) {
    this.clusters = clusters;
    this.classes = classes;
    this.types = types;
    
    this.classInheritanceGraph = classInheritanceGraph;
    this.simpleClassInheritanceGraph = simpleClassInheritanceGraph;
    
    this.classClusterGraph = classClusterGraph;
    this.clusterClusterGraph = clusterClusterGraph;
    
    this.context = Context.getContext();
    this.problems = new Problems();
    consistencyProblems = new Problems();
  }
  
  /**
   * Perform checks on the collected information from the parsing phase
   */
  public void performPreliminaryChecks() {
        
    //Classes with deferred features are deferred themselves
    performDeferrednessChecks();
    //Others?
    checkClassInheritanceForCycles();
    //TODO check cluster containment
    checkClusterContainmentForCycles();
  }
  
  public void checkClassInheritanceForCycles() {
    for (String className : classes.keySet()) {
      Collection<String> cycle = simpleClassInheritanceGraph.findCycle(className, Converter.stringIdentityConverter);
      if (cycle != null) {
        ClassDefinition classDef = classes.get(className);
        classDef.setHasClassHierarchyCycle();
        problems.addProblem(new CycleInRelationsError(classDef.getSourceLocation(), "Class", className, cycle, "class hierarchy"));
      }
    }
  }
  
  public void checkClusterContainmentForCycles() {
    Converter<ClusterDefinition,String> converter = new Converter<ClusterDefinition,String>() {
      public final String convert(final ClusterDefinition toConvert) {
        return toConvert.getClusterName();
      }
    };
    for (String clusterName : clusters.keySet()) {
      Collection<String> cycle = clusterClusterGraph.findCycle(clusterName, converter);
      if (cycle != null) {
        ClusterDefinition clusterDef = clusters.get(clusterName);
        clusterDef.setHasClusterHierarchyCycle();
        problems.addProblem(new CycleInRelationsError(clusterDef.getSourceLocation(), "Cluster", clusterName, cycle, "cluster hierarchy"));
      }
    }
  }
  
  public void performLevelConsistencyChecks(InformalTypingInformation informal) {
    performClassDefinitionLevelConsistencyChecks(informal);
    performClusterDefinitionLevelConsistencyChecks(informal);
  }
  
  public void performClassDefinitionLevelConsistencyChecks(InformalTypingInformation informal) {
    Set<String> informalClasses = informal.getClasses().keySet();
    Set<String> formalClasses = classes.keySet();
    
    for (String informalClass : informalClasses) {
      if (!formalClasses.contains(informalClass)) {
        ClassChartDefinition def = informal.getClasses().get(informalClass);
        consistencyProblems.addProblem(new ClassOrClusterInconsistencyError(def.getSourceLocation(), "Class chart", informalClass, "formal definition"));
      } else {
        //TODO - check inheritance here?
        ClassChartDefinition chartDef = informal.getClasses().get(informalClass);
        ClassDefinition cDef = classes.get(informalClass);
        Collection<String> informalSupers = chartDef.getSuperClasses();
        Collection<String> formalSupers = cDef.getSuperClasses();
        
        for (String informalSuper : informalSupers) {
          if (!formalSupers.contains(informalSuper)) {
            //Super in informal, not in formal
            consistencyProblems.addProblem(new ClassInheritanceInconsistencyError(cDef.getSourceLocation(), "Class", informalClass, informalSuper, "class chart"));
          }
        }
        for (String formalSuper : formalSupers) {
          if (!informalSupers.contains(formalSuper)) {
            //Super in formal, not in informal
            consistencyProblems.addProblem(new ClassInheritanceInconsistencyError(chartDef.getSourceLocation(), "Class chart", informalClass, formalSuper, "formal definition"));
          }
        }
      }
    }
    for (String formalClass : formalClasses) {
      if (!informalClasses.contains(formalClass)) {
        ClassDefinition def = classes.get(formalClass);
        consistencyProblems.addProblem(new ClassOrClusterInconsistencyError(def.getSourceLocation(), "Class", formalClass, "class chart"));
      }
    }
  }
  
  public void performClusterDefinitionLevelConsistencyChecks(InformalTypingInformation informal) {
    Set<String> formalClusters = clusters.keySet();
    Set<String> informalClusters = informal.getClusters().keySet();
    for (String informalCluster : informalClusters) {
      if (!formalClusters.contains(informalCluster)) {
        ClusterChartDefinition def = informal.getClusters().get(informalCluster);
        consistencyProblems.addProblem(new ClassOrClusterInconsistencyError(def.getSourceLocation(), "Cluster chart", informalCluster, "formal definition"));
      }
    }
    for (String formalCluster : formalClusters) {
      if (!informalClusters.contains(formalCluster)) {
        ClusterDefinition def = clusters.get(formalCluster);
        consistencyProblems.addProblem(new ClassOrClusterInconsistencyError(def.getSourceLocation(), "Cluster", formalCluster, "cluster chart"));
      }
    }
  }
  
  public void performDeferrednessChecks() {
    for (ClassDefinition classDef : classes.values()) {
      performDeferrednessChecks(classDef);
    }
  }
  
  private void performDeferrednessChecks(ClassDefinition classDef) {
    if (!classDef.isEffective()) {
      return;
    }
    Set<Type> parents = classDef.getParentClasses();
    
    for (Type t : parents) {
      if (!t.hasGenerics()) {
        ClassDefinition parent = classes.get(t.toString());
        if (parent != null) {
          if (parent.isDeferred()) {
            performDeferrednessChecks(classDef,parent);
          }
        } else {
          //Do anything?
        }
      } else {
        //TODO work with generics here...
      }
    }
  }
  
  private void performDeferrednessChecks(ClassDefinition effectiveChild, ClassDefinition deferredParent) {
    Collection<FeatureSpecificationInstance> deferredFeatures = deferredParent.getDeferredFeatures();
    for (FeatureSpecificationInstance feature : deferredFeatures) {
      //TODO does it have to be labelled effective to override?
      if (!effectiveChild.containsFeatureByName(feature.getName())) {
        problems.addProblem(new EffectiveClassDoesNotDefineDeferredFeatureError(
                                            effectiveChild.getSourceLocation(),
                                            feature.getName(),
                                            effectiveChild.getClassName(),
                                            deferredParent.getClassName()
        ));
      }
    }
  }
  
  public void checkValidClassTypeByContext(String className, SourceLocation loc) {
    if (context.isInSelectiveExport()) {
      checkValidClassType(className, loc, false);
    }
  }
  
  public void checkValidStaticRef(String prefix, SourceLocation prefixLoc, String componentName, SourceLocation componentNameLoc) {
    boolean isClass = isClass(componentName);
    boolean isCluster = isCluster(componentName);
    
    if (!isClass && !isCluster) {
      problems.addProblem(new InvalidStaticComponentTypeError(componentNameLoc, componentName));
    }
    
    if (prefix != null) {
      prefix = prefix.substring(0, prefix.length()-1); //Lob off trailing "."
      String[] bits = prefix.contains(".") ? prefix.split("\\.") : new String[] { prefix } ;
      int offset = 0;
      for (int i=0; i < bits.length-1; i++) {
        if (clusters.containsKey(bits[i])) {
          //Check this cluster contains the following cluster
          if (!isClusterInCluster(bits[i+1], bits[i])) {
            problems.addProblem(new NotContainedInClusterError(prefixLoc,bits[i+1],false,bits[i]));
          }
        } else {
          problems.addProblem(new InvalidClusterTypeError(prefixLoc,bits[i]));
        }
        offset += bits[i].length() + 1;
      }
      
      //Finally check final "bit" is a valid cluster.
      String finalBit = bits[bits.length-1];
      if (clusters.containsKey(finalBit)) {
        //Check for containment
        if (isClass || isCluster) {          
          boolean classContainment = isClass && isClassInCluster(componentName,finalBit);
          boolean clusterContainment = isCluster && isClusterInCluster(componentName,finalBit);
          
          if (!classContainment && !clusterContainment) {
            problems.addProblem(new NotContainedInClusterError(componentNameLoc,componentName,isClass,finalBit));
          }
        }
      } else {        
        problems.addProblem(new InvalidClusterTypeError(prefixLoc,finalBit));
      }
    } 
  }
  
  public final boolean isClassInCluster(String className, String clusterName) {
    Set<ClusterDefinition> clustersClassIsIn = classClusterGraph.getLinkedNodes(className);
    if (clustersClassIsIn != null) {
      ClusterDefinition cluster = clusters.get(clusterName);
      if (cluster != null) {
        return clustersClassIsIn.contains(cluster);
      }
    }
    return false;
  }
  
  public final boolean isClusterInCluster(String clusterName, String containingClusterName) {
    Set<ClusterDefinition> clustersClusterIsIn = clusterClusterGraph.getLinkedNodes(clusterName);
    if (clustersClusterIsIn != null) {
      ClusterDefinition containingCluster = clusters.get(containingClusterName);
      if (containingCluster != null) {
        return clustersClusterIsIn.contains(containingCluster);
      }
    }
    return false;
  }  
  
  public final boolean isClass(String className) {
    return classes.containsKey(className);
  }
  
  public final boolean isCluster(String clusterName) {
    return clusters.containsKey(clusterName);
  }
  
  public void checkValidClassType(String className, SourceLocation loc, boolean canContainGenerics) {
    if (canContainGenerics) {
      Type type = getType(className);
      String actualClassPart = type.getNonGenericType();
      ClassDefinition def = classes.get(actualClassPart);
      if (def == null) {
        problems.addProblem(new InvalidFormalClassTypeError(loc, actualClassPart));
      } else {
        if (type.hasGenerics() && !def.hasFormalGenerics()) {
          problems.addProblem(new ClassIsNotGenericError(loc, def.getClassName()));
        } else {
          //TODO - check appropriate number of generics, appropriate type, etc...
        }
      }

    } else {
      if (!classes.containsKey(className)) {
        problems.addProblem(new InvalidFormalClassTypeError(loc, className));
      }
    }

  }
  
  public void checkType(Type t, SourceLocation loc) {
    Type req = context.currentTypeRequirement();
    if (req != null) {
      if (!t.equals(req)) {
        //TODO - If not a basic type, we can go for inheritance here... Is this ever necessary?
        problems.addProblem(new TypeMismatch(loc, t.toString(), req.toString()));
        Main.logDebug("Type mismatch - current " + t + ", req: " + req);
      }
    }
  }
  
  public void checkType(String t, SourceLocation loc) {
    checkType(getType(t), loc);
  }
  
  public String computeClassInheritanceCycleString(String className) {
    Stack<String> currentPath = new Stack<String>();
    Stack<SortedSet<String>> waitingPaths = new Stack<SortedSet<String>>();
    
    Set<String> explored = new HashSet<String>();
    
    currentPath.push(className);
    
    while (currentPath.size() > 0) {
      
      String currentToExplore = currentPath.peek();
      TreeSet<String> currentParents = new TreeSet<String>(getParentsForClassName(currentToExplore));
      
      if (currentParents.contains(className)) {
        //Match, return String of cycle
        StringBuffer sb = new StringBuffer();
        for (String name : currentPath) {
          sb.append(name);
          sb.append("->");
        }
        sb.append(className);
        return sb.toString();
      }
      
      currentParents.removeAll(explored);
      
      if (currentParents.size() > 0) {
        String first = currentParents.first();
        currentPath.push(first);
        currentParents.remove(first);
        waitingPaths.push(currentParents);
      } else {
        currentPath.pop();
        SortedSet<String> waiting = waitingPaths.peek();
        if (waiting.size() > 0) {
          String first = waiting.first();
          currentPath.push(first);
          waiting.remove(first);
        } else {
          waitingPaths.pop();
        }
      }
    }
    
    return null;
  }
  
  private ClassDefinition getClassDefinitionForTopLevelOfType(Type t) {
    return classes.get(t.getNonGenericType());
  }
  
  public Type getTypeForCall(String x, SourceLocation loc) {
    Main.logDebug("Getting type for call. x=" + x + ", loc - " + loc);
    Type t = context.getLastCallChainType();
    ClassDefinition classDef = null;
    
    if (t == null) {
      Main.logDebug("No last type before " + x + ", so using current class: " + context.getClassName());
      String className = context.getClassName();
      classDef = classes.get(className);
    } else {
      classDef = getClassDefinitionForTopLevelOfType(t);
    }
    
    if (classDef != null) {
      //TODO - inheritance!
      FeatureSpecificationInstance fsi = classDef.getFeatureByName(x);
      if (fsi == null) {
        problems.addProblem(new ClassDoesNotDeclareFeatureError(loc, classDef.getClassName(), x));
      } else {
        t = fsi.getFeatureSpec().getType();
        Main.logDebug("Here with type: " + t);
        return t;
      }
    }
    
    return null;
  }
  
  
  
  private Set<String> getParentsForClassName(String className) {
    ClassDefinition def = classes.get(className);
    return def == null ? null : def.getSimpleParentClasses();
  }
  
  public void checkRenaming(String className, String featureName, SourceLocation loc) {
    ClassDefinition parent = classes.get(className);
    if (parent != null && !parent.containsFeatureByName(featureName)) {
      problems.addProblem(new ClassDoesNotDeclareFeatureError(loc, className, featureName));
    }
    
  }
  
  public Type getType(String typeString) {
    Type type = types.get(typeString);
    if (type == null) {
      type = new Type(typeString, types);
    }
    return type;
  }

  public Problems getProblems() {
    return problems;
  }
  
  public Problems getConsistencyProblems() {
    return consistencyProblems;
  }
  
  
}
