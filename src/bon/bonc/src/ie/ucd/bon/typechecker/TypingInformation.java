/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.Main;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.errors.CannotRenameMultipleFeaturesError;
import ie.ucd.bon.typechecker.errors.ClassCannotHaveSelfAsParentError;
import ie.ucd.bon.typechecker.errors.ClassDoesNotHaveAsSuperTypeError;
import ie.ucd.bon.typechecker.errors.DuplicateClassDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateClusterDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateFeatureDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateFormalGenericNameError;
import ie.ucd.bon.typechecker.errors.DuplicateSuperclassWarning;
import ie.ucd.bon.typechecker.errors.NameNotUniqueError;
import ie.ucd.bon.typechecker.errors.StaticTypeCannotHaveGenericsHere;
import ie.ucd.bon.typechecker.informal.InformalTypingInformation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

/**
 * 
 * @author Fintan
 *
 */
public class TypingInformation {

  private final InformalTypingInformation informal;

  private final Problems problems;

  private final Context context;

  private final Map<String,ClusterDefinition> clusters;
  private final Map<String,ClassDefinition> classes;
  private final Map<String,Type> types;

  private final Graph<String,Type> classInheritanceGraph;
  private final Graph<String,String> simpleClassInheritanceGraph; //Non-generic 

  private final Graph<String,ClusterDefinition> classClusterGraph;
  private final Graph<String,ClassDefinition> reverseClassClusterGraph;
  private final Graph<String,ClusterDefinition> clusterClusterGraph;
  private final Graph<String,ClusterDefinition> reverseClusterClusterGraph;
  
  private boolean finallyProcessed;

  public TypingInformation() {
    context = Context.getContext();
    informal = new InformalTypingInformation(context);
    problems = new Problems();
    clusters = new HashMap<String,ClusterDefinition>();
    classes = new HashMap<String,ClassDefinition>();
    types = new HashMap<String,Type>();

    classInheritanceGraph = new Graph<String,Type>();
    simpleClassInheritanceGraph = new Graph<String,String>();

    classClusterGraph = new Graph<String,ClusterDefinition>();
    reverseClassClusterGraph = new Graph<String,ClassDefinition>();
    clusterClusterGraph = new Graph<String,ClusterDefinition>();
    reverseClusterClusterGraph = new Graph<String,ClusterDefinition>();
    
    finallyProcessed = false;
  }

  public void classNameListEntry(String className, SourceLocation loc) {
    informal.classNameListEntry(className, loc);

    if (context.isInSelectiveExport()) {

      if (className.equals("NONE")) {
        //TODO check for already defined selective exports
        context.getFeature().setPrivate();
      } else {
        //TODO check for duplicate export defined and warn.
        context.getFeature().addExport(className);  
      }
    }
  }

  public Problems getProblems() {
    return problems;
  }  

  public void addCluster(String clusterName, SourceLocation loc) {
    ClassDefinition classDef = classes.get(clusterName);
    if (classDef != null) {
      problems.addProblem(new NameNotUniqueError(loc, "Cluster", clusterName, "class", classDef.getSourceLocation().getSourceFile(), classDef.getSourceLocation().getLineNumber()));
    }
    ClusterDefinition def = clusters.get(clusterName);
    if (def == null) {
      def = new ClusterDefinition(clusterName, loc);
      clusters.put(clusterName, def);
    } else {
      //TODO this might not actually be an error... (If we allow clusters to be mentioned in one place and defined elsewhere)
      problems.addProblem(new DuplicateClusterDefinitionError(loc, def));
    }

    if (context.isInCluster()) {
      clusterClusterGraph.addEdge(clusterName, clusters.get(context.getInnermostCluster()));
      reverseClusterClusterGraph.addEdge(context.getInnermostCluster(), clusters.get(clusterName));
    } 
  }

  public void addClass(String className, SourceLocation loc, String keyword) {
    ClusterDefinition clusterDef = clusters.get(className);
    if (clusterDef != null) {
      problems.addProblem(new NameNotUniqueError(loc, "Class", className, "cluster", clusterDef.getSourceLocation().getSourceFile(), clusterDef.getSourceLocation().getLineNumber()));
    }
    ClassDefinition def = classes.get(className);
    if (def == null) {
      def = new ClassDefinition(className, loc, this);

      if (keyword != null) {
        if (keyword.equals("root")) {
          def.setRoot();
        } else if (keyword.equals("deferred")) {
          def.setDeferred();
        } else if (keyword.equals("effective")) {
          def.setEffective();
        }
      }

      classes.put(className, def);
    } else {
      //TODO this might not actually be an error... (If we allow classes to be mentioned in one place and defined elsewhere)
      problems.addProblem(new DuplicateClassDefinitionError(loc, def));
    }

    if (context.isInCluster()) {
      classClusterGraph.addEdge(className, clusters.get(context.getInnermostCluster()));
      reverseClassClusterGraph.addEdge(context.getInnermostCluster(), def);
    } 
  }

  public Type getType(String typeString) {
    Type type = types.get(typeString);
    if (type == null) {
      type = new Type(typeString, types);
    }
    return type;
  }

  public void formalGeneric(String name, String typeString, SourceLocation loc) {
    if (context.isInClass()) {
      ClassDefinition def = classes.get(context.getClassName());
      if (def.hasFormalGeneric(name)) {
        //Error, duplicate generic name   
        problems.addProblem(new DuplicateFormalGenericNameError(loc, name));
      } else {
        Type type = null;
        if (typeString != null) {
          type = getType(typeString);
        }
        def.addFormalGeneric(name, type, loc); 
      }      
    }
  }
  
  public void addParent(String parent, SourceLocation loc) {
    addParent(context.getClassName(), parent, loc);
  }
  
  public void addParent(String child, String parent, SourceLocation loc) {
    //Handle static refs
    String[] actualChildParts = child.contains(".") ? child.split("\\.") : new String[] {child};
    String actualChild = actualChildParts[actualChildParts.length-1];
    String[] actualParentParts = parent.contains(".") ? parent.split("\\.") : new String[] {parent};
    String actualParent = actualParentParts[actualParentParts.length-1];
    
    Type parentType = getType(actualParent);
    Type childType = getType(actualChild);
    
    if (childType.hasGenerics()) {
      problems.addProblem(new StaticTypeCannotHaveGenericsHere(loc, childType.getNonGenericType(), " as the child in an inheritance relation."));
    } else {

      if (parentType.getNonGenericType().equals(actualChild)) {
        problems.addProblem(new ClassCannotHaveSelfAsParentError(loc, actualChild));
      } else {
        if (simpleClassInheritanceGraph.hasEdge(actualChild, parentType.getNonGenericType())) {
          problems.addProblem(new DuplicateSuperclassWarning(loc, actualChild, actualParent));
        } else {
          classInheritanceGraph.addEdge(actualChild, parentType);
          simpleClassInheritanceGraph.addEdge(actualChild, parentType.getNonGenericType());
        }
      }
    }
  }

  public void addInvariant(String invariant, SourceLocation loc) {
    String currentClassName = context.getClassName();
    ClassDefinition classDef = classes.get(currentClassName);
    if (classDef != null) {
      classDef.addInvariant(invariant);
    }
  }

  public void setPrecondition(String precondition, SourceLocation loc) {
    context.getFeatureSpec().setPrecondition(precondition);
  }

  public void setPostcondition(String postcondition, SourceLocation loc) {
    context.getFeatureSpec().setPostcondition(postcondition);
  }

  public void featureSpecDeferred() {
    context.getFeatureSpec().setDeferred(); 
  } 
  public void featureSpecEffective(){ 
    context.getFeatureSpec().setEffective(); 
  }
  public void featureSpecRedefined() {
    context.getFeatureSpec().setRedefined();
  }

  public void featureNameListEntry(String name, SourceLocation loc) {
    if (context.isInFeatureSpecification()) {
      FeatureSpecificationInstance instance = new FeatureSpecificationInstance(name, context.getFeatureSpec(), loc);

      ClassDefinition def = classes.get(context.getClassName());
      if (def.containsFeatureByName(name)) {
        FeatureSpecificationInstance other = def.getFeatureByName(name);
        problems.addProblem(new DuplicateFeatureDefinitionError(instance.getSourceLocation(), other));
      } else {
        def.addFeature(instance);
      }
    }
  }

  public void renaming(String className, String featureName, SourceLocation loc) {
    boolean valid = true;

    FeatureSpecification current = context.getFeatureSpec();

    if (current.getNumberOfInstances() > 1) {
      problems.addProblem(new CannotRenameMultipleFeaturesError(loc));
    }

    //TODO - if we allow other ways of defining inheritance (inheritance relations)
    //       then this cannot be done here.
    ClassDefinition def = classes.get(context.getClassName());
    if (!def.getSimpleParentClasses().contains(className)) {
      problems.addProblem(new ClassDoesNotHaveAsSuperTypeError(loc, context.getClassName(), className));
      valid = false;
    } 

    if (valid) {
      context.getFeatureSpec().setRenaming(className, featureName);
    }
  }

  public void featureArg(String names, String type) {
    Type t = getType(type);
    if (names != null) {
      String[] parts = names.split(",");
      for (String s : parts) {
        s = s.trim();
        context.getFeatureSpec().addArgument(s, t);
      }
    } else {
      context.getFeatureSpec().addArgument(null, t);
    }
  }

  public void hasType(String typeString) {
    context.getFeatureSpec().setType(getType(typeString));
  }

  public InformalTypingInformation informal() {
    return informal;
  }

  //For Graphing
  public Map<String, ClusterDefinition> getClusters() {
    return clusters;
  }

  public Map<String, ClassDefinition> getClasses() {
    return classes;
  }

  public void setDescription(String description) {
    //Currently nothing here

    informal.setDescription(description);
  }

  public FormalTypeChecker getFormalTypeChecker() {
    finalProcess(); //Ensure finally processed
    return new FormalTypeChecker(clusters, classes, types, classInheritanceGraph, simpleClassInheritanceGraph, classClusterGraph, clusterClusterGraph);
  }
  
  public void finalProcess() {
    if (!finallyProcessed) {
      expandClusterInheritanceToClasses();
      finallyProcessed = true;
    }
  }
  
  private void expandClusterInheritanceToClasses() {
    Main.logDebug("Expanding cluster inheritance.");
    Main.logDebug("Simple class inherit graph before: \n" + simpleClassInheritanceGraph);
    Set<Entry<String,Set<Type>>> complexEdges = classInheritanceGraph.getEdges();
    
    for (Entry<String,Set<Type>> edge : new ArrayList<Entry<String,Set<Type>>>(complexEdges)) {
      String childName = edge.getKey();
      Set<Type> parentTypes = edge.getValue();
      
      Main.logDebug("Edge: " + childName + " -> " + parentTypes);
      
      Set<ClassDefinition> childClasses = getClassesForType(childName);
      Main.logDebug("Child classes: " + childClasses);
      
      for (ClassDefinition childDef : childClasses) {
        for (Type parentType : new ArrayList<Type>(parentTypes)) {
          //If parent is class, do nothing...
          
          if (!classes.containsKey(parentType.getNonGenericType()) && clusters.containsKey(parentType.getNonGenericType())) {
            Main.logDebug("It's a cluster.");
            Set<ClassDefinition> parentClasses = getClassesForType(parentType.getNonGenericType());
            Main.logDebug("Actual parents: " + parentClasses);
            
            //First remove original link from child to parent (cluster)
            boolean removedSimpleEdge = simpleClassInheritanceGraph.removeEdge(childName, parentType.getNonGenericType());
            boolean removedComplexEdge = classInheritanceGraph.removeEdge(childName, parentType);
            if (!removedSimpleEdge) { Main.logDebug("No simple edge to remove: " + childName + ", " + parentType.getNonGenericType()); }
            if (!removedComplexEdge) { Main.logDebug("No complex edge to remove: " + childName + ", " + parentType); }
            
            //Then add new links for all the parent classes, simple and full (although all have no generics).  
            for (ClassDefinition parentDef : parentClasses) {
              if (parentDef.equals(childDef)) {
                problems.addProblem(new ClassCannotHaveSelfAsParentError(childDef.getSourceLocation(), childDef.getClassName()));
              } else {
                simpleClassInheritanceGraph.addEdge(childDef.getClassName(), parentDef.getClassName());
                classInheritanceGraph.addEdge(childDef.getClassName(), getType(parentDef.getClassName()));
              }
            }
          } else {
            Main.logDebug(parentType.getNonGenericType() + " is not a class.");
          }
        }
      }
    }
    Main.logDebug("Simple class inherit graph after: \n" + simpleClassInheritanceGraph);
  }
  
  private Set<ClassDefinition> getClassesForType(String type) {
    Set<ClassDefinition> theClasses;
    if (classes.containsKey(type)) {
      theClasses = new HashSet<ClassDefinition>();
      theClasses.add(classes.get(type));
    } else if (clusters.containsKey(type)) {
      theClasses = getClassesInCluster(type, new HashSet<ClusterDefinition>());
    } else {
      theClasses = new HashSet<ClassDefinition>();
    }
    return theClasses;
  }
  
  private Set<ClassDefinition> getClassesInCluster(String clusterName, Set<ClusterDefinition> seen) {
    seen.add(clusters.get(clusterName));
    
    Set<ClassDefinition> classes = reverseClassClusterGraph.getLinkedNodes(clusterName);
    Set<ClusterDefinition> clusters = reverseClusterClusterGraph.getLinkedNodes(clusterName);
    
    for (ClusterDefinition cluster : clusters) {
      if (!seen.contains(cluster)) {
        classes.addAll(getClassesInCluster(cluster.getClusterName(), seen));
      }
    }
    
    return classes;
  }

  public Graph<String, Type> getClassInheritanceGraph() {
    return classInheritanceGraph;
  }

  public Graph<String, String> getSimpleClassInheritanceGraph() {
    return simpleClassInheritanceGraph;
  }

  public Graph<String, ClusterDefinition> getClassClusterGraph() {
    return classClusterGraph;
  }

  public Graph<String, ClusterDefinition> getClusterClusterGraph() {
    return clusterClusterGraph;
  }

  public void setClassReused() {
    if (context.isInClass()) {
      ClassDefinition def = classes.get(context.getClassName());
      if (def != null) {
        def.setReused(true);
      }
    }
  }

  public void setClassPersistent() {
    if (context.isInClass()) {
      ClassDefinition def = classes.get(context.getClassName());
      if (def != null) {
        def.setPersistent(true);
      }
    }
  }

  public void setClassInterfaced() {
    if (context.isInClass()) {
      ClassDefinition def = classes.get(context.getClassName());
      if (def != null) {
        def.setInterfaced(true);
      }
    }
  }

}

