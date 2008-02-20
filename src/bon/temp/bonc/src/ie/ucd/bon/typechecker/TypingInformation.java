/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.parser.SourceLocation;
import ie.ucd.bon.typechecker.errors.CannotRenameMultipleFeaturesError;
import ie.ucd.bon.typechecker.errors.ClassCannotHaveSelfAsParentError;
import ie.ucd.bon.typechecker.errors.ClassDoesNotHaveAsSuperTypeError;
import ie.ucd.bon.typechecker.errors.DuplicateClassDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateClusterDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateFeatureDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateFormalGenericNameError;
import ie.ucd.bon.typechecker.errors.DuplicateSuperclassWarning;
import ie.ucd.bon.typechecker.informal.ClusterChartDefinition;
import ie.ucd.bon.typechecker.informal.InformalTypingInformation;

import java.util.HashMap;
import java.util.Map;

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
  private final Graph<String,ClusterDefinition> clusterClusterGraph;
    
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
    clusterClusterGraph = new Graph<String,ClusterDefinition>();
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
    } 
  }
  
  public void addClass(String className, SourceLocation loc, String keyword) {
    ClassDefinition def = classes.get(className);
    if (def == null) {
      def = new ClassDefinition(className, loc);
      
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
  
  public void addParentClass(String parent, SourceLocation loc) {
    Type parentType = getType(parent);
    String currentClassName = context.getClassName();
    if (parentType.getNonGenericType().equals(currentClassName)) {
      problems.addProblem(new ClassCannotHaveSelfAsParentError(loc, currentClassName));
    } else {
     
      if (simpleClassInheritanceGraph.hasEdge(currentClassName,parentType.getNonGenericType())) {
        problems.addProblem(new DuplicateSuperclassWarning(loc,currentClassName,parent));
      } else {
        classInheritanceGraph.addEdge(currentClassName, parentType);
        simpleClassInheritanceGraph.addEdge(currentClassName, parentType.getNonGenericType());
        ClassDefinition def = classes.get(currentClassName);
        def.addParentClass(parentType);
      }
    }
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
      if (def.constainsFeatureByName(name)) {
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

  /*public Map<String, ClusterDefinition> getClusterClusterContainsLink() {
    return clusterClusterContainsLink;
  }

  public Map<String, ClusterDefinition> getClassClusterContainsLink() {
    return classClusterContainsLink;
  }*/
  
  public FormalTypeChecker getFormalTypeChecker() {
    return new FormalTypeChecker(clusters, classes, types, classInheritanceGraph, simpleClassInheritanceGraph, classClusterGraph, clusterClusterGraph);
  }
  
}

