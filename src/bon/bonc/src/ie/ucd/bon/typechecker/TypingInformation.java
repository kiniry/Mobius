/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.Main;
import ie.ucd.bon.ast.BONType;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.ast.TypeMark;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.errors.CannotRenameMultipleFeaturesError;
import ie.ucd.bon.typechecker.errors.ClassCannotHaveSelfAsParentError;
import ie.ucd.bon.typechecker.errors.ClassDoesNotHaveAsSuperTypeError;
import ie.ucd.bon.typechecker.errors.DeferredFeatureInNonDeferredClassError;
import ie.ucd.bon.typechecker.errors.DuplicateClassDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateClusterDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateFeatureDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateFormalGenericNameError;
import ie.ucd.bon.typechecker.errors.DuplicateSuperclassWarning;
import ie.ucd.bon.typechecker.errors.NameNotUniqueError;
import ie.ucd.bon.typechecker.errors.StaticTypeCannotHaveGenericsHere;
import ie.ucd.bon.typechecker.informal.InformalTypingInformation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
  private final Map<String,BONType> types;

  private final Graph<String,BONType> classInheritanceGraph;
  private final Graph<String,String> simpleClassInheritanceGraph; //Non-generic 

  private final Graph<String,ClusterDefinition> classClusterGraph;
  private final Graph<String,ClassDefinition> reverseClassClusterGraph;
  private final Graph<String,ClusterDefinition> clusterClusterGraph;
  private final Graph<String,ClusterDefinition> reverseClusterClusterGraph;

  private final List<ClientRelation> clientRelations;

  private boolean finallyProcessed;

  public TypingInformation() {
    context = Context.getContext();
    informal = new InformalTypingInformation(context);
    problems = new Problems("TI");
    clusters = new HashMap<String,ClusterDefinition>();
    classes = new HashMap<String,ClassDefinition>();
    types = new HashMap<String,BONType>();

    classInheritanceGraph = new Graph<String,BONType>();
    simpleClassInheritanceGraph = new Graph<String,String>();

    classClusterGraph = new Graph<String,ClusterDefinition>();
    reverseClassClusterGraph = new Graph<String,ClassDefinition>();
    clusterClusterGraph = new Graph<String,ClusterDefinition>();
    reverseClusterClusterGraph = new Graph<String,ClusterDefinition>();

    clientRelations = new LinkedList<ClientRelation>();

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
      problems.addProblem(new NameNotUniqueError(loc, "Cluster", clusterName, "class", classDef.getSourceLocation()));
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
      clusterClusterGraph.put(clusterName, clusters.get(context.getInnermostCluster()));
      reverseClusterClusterGraph.put(context.getInnermostCluster(), clusters.get(clusterName));
    } 
  }

  public void addClass(String className, SourceLocation loc, Clazz.Mod mod) {
    ClusterDefinition clusterDef = clusters.get(className);
    if (clusterDef != null) {
      problems.addProblem(new NameNotUniqueError(loc, "Class", className, "cluster", clusterDef.getSourceLocation()));
    }
    ClassDefinition def = classes.get(className);
    if (def == null) {
      def = new ClassDefinition(className, loc, this);
      
      switch (mod) {
      case DEFERRED:
        def.setDeferred();
      case ROOT:
        def.setRoot();
      case EFFECTIVE:
        def.setEffective();
      }

      classes.put(className, def);
    } else {
      //TODO this might not actually be an error... (If we allow classes to be mentioned in one place and defined elsewhere)
      problems.addProblem(new DuplicateClassDefinitionError(loc, def));
    }

    if (context.isInCluster()) {
      classClusterGraph.put(className, clusters.get(context.getInnermostCluster()));
      reverseClassClusterGraph.put(context.getInnermostCluster(), def);
    } 
  }

  public void formalGeneric(String name, String typeString, SourceLocation loc) {
    if (context.isInClass()) {
      ClassDefinition def = classes.get(context.getClassName());
      if (def.hasFormalGeneric(name)) {
        //Error, duplicate generic name   
        problems.addProblem(new DuplicateFormalGenericNameError(loc, name));
      } else {
        BONType type = null;
        if (typeString != null) {
          type = BONType.mk(typeString);
        }
        def.addFormalGeneric(name, type, loc); 
      }      
    }
  }

  public void addParent(BONType parent, SourceLocation loc) {
    addParent(BONType.mk(context.getClassName(), null, context.getClassName(), loc), parent, loc);
  }

  public void addParent(BONType child, BONType parent, SourceLocation loc) {
    if (child != null && parent != null) {
      if (child.hasGenerics()) {
        problems.addProblem(new StaticTypeCannotHaveGenericsHere(loc, child.getNonGenericType(), " as the child in an inheritance relation."));
      } else {
        if (parent.getNonGenericType().equals(child.getNonGenericType())) {
          problems.addProblem(new ClassCannotHaveSelfAsParentError(loc, child.getFullString()));
        } else {
          if (simpleClassInheritanceGraph.containsEntry(child.getFullString(), parent.getNonGenericType())) {
            problems.addProblem(new DuplicateSuperclassWarning(loc, child.getFullString(), parent.getFullString()));
          } else {
            classInheritanceGraph.put(child.getFullString(), parent);
            simpleClassInheritanceGraph.put(child.getFullString(), parent.getNonGenericType());
          }
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

  private void featureSpecDeferred() {
    context.getFeatureSpec().setDeferred(); 
    String currentClass = context.getClassName();
    if (currentClass != null) {
      ClassDefinition classDef = classes.get(currentClass);
      if (classDef != null && !classDef.isDeferred()) {
        FeatureSpecification featureSpec = context.getFeatureSpec();
        List<FeatureSpecificationInstance> instances = featureSpec.getInstances();
        SourceLocation loc;
        if (instances.size() > 1) {
          loc = instances.get(0).getSourceLocation();
        } else {
          loc = new SourceLocation(instances.get(0).getSourceLocation(), instances.get(instances.size()-1).getSourceLocation());
        }
        StringBuilder sb = new StringBuilder();
        for (FeatureSpecificationInstance instance : instances) {
          sb.append(instance.getName());
          sb.append(", ");
        }
        if (sb.length() >= 2) {
          sb.delete(sb.length()-2, sb.length());
        }

        problems.addProblem(new DeferredFeatureInNonDeferredClassError(loc, sb.toString(), context.getClassName()));
      }
    }
  } 
  private void featureSpecEffective(){ 
    context.getFeatureSpec().setEffective(); 
  }
  private void featureSpecRedefined() {
    context.getFeatureSpec().setRedefined();
  }
  
  public void featureSpecModifier(ie.ucd.bon.ast.FeatureSpecification.Modifier modifier) {
	switch(modifier) {
	case DEFERRED:
		featureSpecDeferred();
		break;
	case EFFECTIVE:
		featureSpecEffective();
		break;
	case REDEFINED:
		featureSpecRedefined();
		break;
	}
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
    Type t = BONType.mk(type);
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

  public void hasType(TypeMark mark, String typeString) {
    context.getFeatureSpec().setType(mark, BONType.mk(typeString));
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
    
    //Collection<Entry<String,BONType>> complexEdges = classInheritanceGraph.entries();
    Set<String> classNames = classInheritanceGraph.keySet();

    //for (Entry<String,Set<BONType>> edge : new ArrayList<Entry<String,Set<BONType>>>(complexEdges)) {
    for (String childName : classNames) {
      Collection<BONType> parentTypes = classInheritanceGraph.get(childName);

      Main.logDebug("Edge: " + childName + " -> " + parentTypes);

      Collection<ClassDefinition> childClasses = getClassesForType(childName);
      Main.logDebug("Child classes: " + childClasses);

      for (ClassDefinition childDef : childClasses) {
        for (BONType parentType : new ArrayList<BONType>(parentTypes)) {
          //If parent is class, do nothing...

          if (!classes.containsKey(parentType.getNonGenericType()) && clusters.containsKey(parentType.getNonGenericType())) {
            Main.logDebug("It's a cluster.");
            Collection<ClassDefinition> parentClasses = getClassesForType(parentType.getNonGenericType());
            Main.logDebug("Actual parents: " + parentClasses);

            //First remove original link from child to parent (cluster)
            boolean removedSimpleEdge = simpleClassInheritanceGraph.remove(childName, parentType.getNonGenericType());
            boolean removedComplexEdge = classInheritanceGraph.remove(childName, parentType);
            if (!removedSimpleEdge) { Main.logDebug("No simple edge to remove: " + childName + ", " + parentType.getNonGenericType()); }
            if (!removedComplexEdge) { Main.logDebug("No complex edge to remove: " + childName + ", " + parentType); }

            //Then add new links for all the parent classes, simple and full (although all have no generics).  
            for (ClassDefinition parentDef : parentClasses) {
              if (parentDef.equals(childDef)) {
                problems.addProblem(new ClassCannotHaveSelfAsParentError(childDef.getSourceLocation(), childDef.getName()));
              } else {
                simpleClassInheritanceGraph.put(childDef.getName(), parentDef.getName());
                classInheritanceGraph.put(childDef.getName(), BONType.mk(parentDef.getName()));
              }
            }
          } else {
            Main.logDebug(parentType.getNonGenericType() + " is not a cluster.");
          }
        }
      }
    }
    Main.logDebug("Simple class inherit graph after: \n" + simpleClassInheritanceGraph);
  }

  private Collection<ClassDefinition> getClassesForType(String type) {
    Collection<ClassDefinition> theClasses;
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

  private Collection<ClassDefinition> getClassesInCluster(String clusterName, Set<ClusterDefinition> seen) {
    seen.add(clusters.get(clusterName));

    Collection<ClassDefinition> classes = reverseClassClusterGraph.get(clusterName);
    Collection<ClusterDefinition> clusters = reverseClusterClusterGraph.get(clusterName);

    for (ClusterDefinition cluster : clusters) {
      if (!seen.contains(cluster)) {
        classes.addAll(getClassesInCluster(cluster.getName(), seen));
      }
    }

    return classes;
  }

  public Graph<String, BONType> getClassInheritanceGraph() {
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

  public void addClientRelation() {
    clientRelations.add(context.getClientRelation());
  }

  public List<ClientRelation> getClientRelations() {
    return clientRelations;
  }

  public void typeMark(TypeMark mark) {
    if (context.isInClientRelation()) {
      context.getClientRelation().setTypeMark(mark);
    }
  }

  public void indexing(Indexing indexing) {
    if (context.isInClass()) {
      ClassDefinition def = classes.get(context.getClassName());
      if (def != null) {
        def.setIndexing(indexing);
      }
    } else {
      informal.indexing(indexing);
    }
  }

}

