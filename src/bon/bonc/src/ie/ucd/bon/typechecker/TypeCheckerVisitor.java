package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.AbstractVisitor;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClassInterface;
import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClientEntityExpression;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ContractClause;
import ie.ucd.bon.ast.Expression;
import ie.ucd.bon.ast.Feature;
import ie.ucd.bon.ast.FeatureArgument;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.HasType;
import ie.ucd.bon.ast.IVisitor;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.InheritanceRelation;
import ie.ucd.bon.ast.Multiplicity;
import ie.ucd.bon.ast.RenameClause;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.ast.StaticComponent;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.ast.StaticRef;
import ie.ucd.bon.ast.StaticRefPart;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.ast.TypeMark;
import ie.ucd.bon.ast.Clazz.Mod;
import ie.ucd.bon.ast.FeatureSpecification.Modifier;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.errors.ClassCannotHaveSelfAsParentError;
import ie.ucd.bon.typechecker.errors.InvalidClusterTypeError;
import ie.ucd.bon.typechecker.errors.InvalidFormalClassTypeError;
import ie.ucd.bon.typechecker.errors.InvalidStaticComponentTypeError;
import ie.ucd.bon.typechecker.errors.NotContainedInClusterError;
import ie.ucd.bon.typechecker.informal.errors.InvalidInformalClassTypeError;

import java.util.List;

public class TypeCheckerVisitor extends AbstractVisitor implements IVisitor {

  private final BONST st;
  private final Problems problems;

  public TypeCheckerVisitor(BONST st) {
    this.st = st;
    this.problems = new Problems("TC");
  }

  @Override
  public void visitBonSourceFile(BonSourceFile node,
      List<SpecificationElement> bonSpecification, Indexing indexing,
      SourceLocation loc) {

    visitAll(bonSpecification);
  }

  @Override
  public void visitStaticDiagram(StaticDiagram node,
      List<StaticComponent> components, String extendedId, String comment,
      SourceLocation loc) {

    visitAll(components);    
  }



  @Override
  public void visitClientRelation(ClientRelation node, StaticRef client,
      StaticRef supplier, ClientEntityExpression clientEntities,
      TypeMark typeMark, String semanticLabel, SourceLocation loc) {

    visitNode(client);
    visitNode(supplier);
  }

  @Override
  public void visitInheritanceRelation(InheritanceRelation node,
      StaticRef child, StaticRef parent, Multiplicity multiplicity,
      String semanticLabel, SourceLocation loc) {

    if (child.getName().getName().equals(parent.getName().getName())) {
      problems.addProblem(new ClassCannotHaveSelfAsParentError(loc, child.getName().getName()));
    }
    
    visitNode(child);
    visitNode(parent);
  }

  @Override
  public void visitStaticRef(StaticRef node, List<StaticRefPart> prefix, StaticRefPart name, SourceLocation loc) {

    boolean isClass = isClass(name.getName());
    boolean isCluster = isCluster(name.getName());

    if (!isClass && !isCluster) {
      problems.addProblem(new InvalidStaticComponentTypeError(name.getLocation(), name.getName()));          
    }

    if (prefix.size() > 0) {
      StaticRefPart[] prefixArray = prefix.toArray(new StaticRefPart[prefix.size()]);
      for (int i=0; i < prefixArray.length-1; i++) {
        StaticRefPart current = prefixArray[i];
        StaticRefPart next = prefixArray[i+1];
        if (isCluster(current.getName())) {
          if (!isClusterInCluster(next.getName(), current.getName())) {
            problems.addProblem(new NotContainedInClusterError(new SourceLocation(current.getLocation(), next.getLocation()), next.getName(), false, current.getName()));
          }
        } else {
          problems.addProblem(new InvalidClusterTypeError(current.getLocation(), current.getName()));
        }
      }

      StaticRefPart finalPrefix = prefixArray[prefixArray.length-1];
      if (st.clusters.containsKey(finalPrefix.getName())) {
        if (isClass) {
          //It's a class, check class is in cluster
          if (!isClassInCluster(name.getName(), finalPrefix.getName())) {
            problems.addProblem(new NotContainedInClusterError(new SourceLocation(finalPrefix.getLocation(), name.getLocation()), name.getName(), true, finalPrefix.getName()));
          }
        } else if (isCluster) {
          //It's a cluster, check cluster is in cluster
          if (!isClusterInCluster(name.getName(), finalPrefix.getName())) {
            problems.addProblem(new NotContainedInClusterError(new SourceLocation(finalPrefix.getLocation(), name.getLocation()), name.getName(), false, finalPrefix.getName()));
          }
        }
      } else {
        problems.addProblem(new InvalidClusterTypeError(finalPrefix.getLocation(), finalPrefix.getName()));
      } 
    }
  }

  @Override
  public void visitClassInterface(ClassInterface node, List<Feature> features,
      List<Type> parents, List<Expression> invariant, Indexing indexing,
      SourceLocation loc) {

    for (Type parent : parents) {
      if (!isClass(parent)) {
        //TODO typecheck these properly..
        problems.addProblem(new InvalidFormalClassTypeError(parent.getLocation(), parent.getIdentifier()));
      }
    }
    
    visitAll(features);
    visitAll(invariant);
  }

  @Override
  public void visitClazz(Clazz node, ClassName name, List<FormalGeneric> generics,
      Mod mod, ClassInterface classInterface, Boolean reused,
      Boolean persistent, Boolean interfaced, String comment, SourceLocation loc) {

    visitNode(classInterface);
  }
  
  @Override
  public void visitFeature(Feature node,
      List<FeatureSpecification> featureSpecifications,
      List<ClassName> selectiveExport, String comment, SourceLocation loc) {
    visitAll(featureSpecifications);
  }

  @Override
  public void visitFeatureSpecification(FeatureSpecification node,
      Modifier modifier, List<String> featureNames,
      List<FeatureArgument> arguments, ContractClause contracts,
      HasType hasType, RenameClause renaming, String comment, SourceLocation loc) {
    
    visitNode(contracts);
  }

  @Override
  public void visitCluster(Cluster node, String name,
      List<StaticComponent> components, Boolean reused, String comment,
      SourceLocation loc) {
    
    visitAll(components);
  }
  
  

  @Override
  public void visitClassChart(ClassChart node, ClassName name,
      List<ClassName> inherits, List<String> queries, List<String> commands,
      List<String> constraints, Indexing indexing, String explanation,
      String part, SourceLocation loc) {
    
    for (ClassName parentName : inherits) {
      if (name.getName().equals(parentName.getName())) {
        problems.addProblem(new ClassCannotHaveSelfAsParentError(name.getLocation(), name.getName()));
      } else if (!isClassChart(parentName.getName())) {
        problems.addProblem(new InvalidInformalClassTypeError(parentName.getLocation(), parentName.getName()));
      }
    }
  }

  private boolean isClass(Type type) {
    return isClass(type.getIdentifier());
  }
  
  private boolean isClass(String name) {
    return st.classes.containsKey(name);
  }
  
  private boolean isCluster(String name) {
    return st.clusters.containsKey(name);
  }
  
  private boolean isClassChart(String name) {
    return st.informal.classes.containsKey(name);
  }
  
  private boolean isClassInCluster(String className, String clusterName) {
    return st.classClusterGraph.containsEntry(className, st.clusters.get(clusterName));
  }
  
  private boolean isClusterInCluster(String containee, String containing) {
    return st.clusterClusterGraph.containsEntry(containee, st.clusters.get(containing));
  }

  public Problems getProblems() {
    return problems;
  }
}
