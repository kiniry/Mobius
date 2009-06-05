package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.AbstractVisitor;
import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BONType;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClassEntry;
import ie.ucd.bon.ast.ClassInterface;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClientEntityExpression;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.ClusterEntry;
import ie.ucd.bon.ast.Expression;
import ie.ucd.bon.ast.Feature;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.IVisitor;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.ast.StaticComponent;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.ast.TypeMark;
import ie.ucd.bon.ast.Clazz.Mod;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.errors.ClassCannotHaveSelfAsParentError;
import ie.ucd.bon.typechecker.errors.DuplicateClassDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateClusterDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateSystemDefinitionError;
import ie.ucd.bon.typechecker.errors.NameNotUniqueError;
import ie.ucd.bon.typechecker.informal.errors.DuplicateClassChartError;
import ie.ucd.bon.typechecker.informal.errors.DuplicateClusterChartError;

import java.util.Collection;
import java.util.List;

public class STBuilderVisitor extends AbstractVisitor implements IVisitor {

  private final BONST st;
  private final Problems problems;
  private final VisitorContext context;

  public STBuilderVisitor(BONST st) {
    this.st = st;
    problems = new Problems("STBuilder");
    context = new VisitorContext();
  }

  public BONST getSt() {
    return st;
  }

  public Problems getProblems() {
    return problems;
  }

  @Override
  public void visitBonSourceFile(BonSourceFile node,
      List<SpecificationElement> bonSpecification, Indexing indexing,
      SourceLocation loc) {
    
    visitAll(bonSpecification);
    indexing(node, indexing);
  }
  
  @Override
  public void visitStaticDiagram(StaticDiagram node,
      List<StaticComponent> components, String extendedId, String comment,
      SourceLocation loc) {
    
    visitAll(components);    
  }

  @Override
  public void visitClazz(Clazz node, String name, List<FormalGeneric> generics,
      Mod mod, ClassInterface classInterface, Boolean reused,
      Boolean persistent, Boolean interfaced, String comment, SourceLocation loc) {

    Clazz clazz = st.classes.get(name);
    Cluster cluster = st.clusters.get(name);

    if (cluster != null) {
      problems.addProblem(new NameNotUniqueError(loc, "Class", name, "cluster", cluster.getLocation()));  
    } else if (clazz != null) {
      problems.addProblem(new DuplicateClassDefinitionError(loc, clazz));
    } else {
      st.classes.put(name, node);

      if (!context.clusterStack.empty()) {
        st.classClusterGraph.put(name, context.clusterStack.peek());
      }
      
      context.clazz = node;
      visitNode(classInterface);
      context.clazz = null;      

    }
  }

  @Override
  public void visitCluster(Cluster node, String name,
      List<StaticComponent> components, Boolean reused, String comment, SourceLocation loc) {

    Clazz clazz = st.classes.get(name);
    Cluster cluster = st.clusters.get(name);

    if (clazz != null) {
      problems.addProblem(new NameNotUniqueError(loc, "Cluster", name, "class", clazz.getLocation()));  
    } else if (cluster != null) {
      problems.addProblem(new DuplicateClusterDefinitionError(loc, cluster));
    } else {
      st.clusters.put(name, node);
    }

    if (!context.clusterStack.empty()) {
      st.clusterClusterGraph.put(name, context.clusterStack.peek());
    }
    
    context.clusterStack.push(node);
    visitAll(components);
    context.clusterStack.pop();
  }

  @Override
  public void visitClassInterface(ClassInterface node, List<Feature> features,
      List<BONType> parents, List<Expression> invariant, Indexing indexing,
      SourceLocation loc) {
    
    for (BONType parent : parents) {
      st.classInheritanceGraph.put(context.clazz.getName(), parent);
      st.simpleClassInheritanceGraph.put(context.clazz.getName(), parent.getIdentifier());
    }
    
    //TODO proper ST for feature
    visitAll(features);
    visitAll(invariant);

    indexing(context.clazz, indexing);
  }



  @Override
  public void visitClassChart(ClassChart node, String name,
      List<String> inherits, List<String> queries, List<String> commands,
      List<String> constraints, Indexing indexing, String explanation,
      String part, SourceLocation loc) {
    
    //Check if name unique
    ClusterChart otherCluster = st.informal.clusters.get(name);
    if (otherCluster != null) {
      problems.addProblem(new NameNotUniqueError(loc, "Cluster", name, "class", otherCluster.getLocation()));
    }else {
      ClassChart clazz = st.informal.classes.get(name);
      if (clazz != null) {
        problems.addProblem(new DuplicateClassChartError(loc, clazz));  
      } else {
        st.informal.classes.put(name, node);
      }
    }

    for (String parent : inherits) {
      if (parent.equals(name)) {
        problems.addProblem(new ClassCannotHaveSelfAsParentError(loc, name));
      } else {
        st.informal.classInheritanceGraph.put(node, parent);      
      }
    }
    
    indexing(node, indexing);
  }

  @Override
  public void visitClusterChart(ClusterChart node, String name, Boolean isSystem,
      List<ClassEntry> classes, List<ClusterEntry> clusters, Indexing indexing,
      String explanation, String part, SourceLocation loc) {

    //If system, set system
    if (isSystem) {
      if (st.informal.systemChart != null) {
        //Duplicate system, add error.
        problems.addProblem(new DuplicateSystemDefinitionError(loc, node));
        return;
      } else {
        st.informal.systemChart = node;
      }
    }

    //Check if name unique
    ClassChart otherClass = st.informal.classes.get(name);
    if (otherClass != null) {
      problems.addProblem(new NameNotUniqueError(loc, "Cluster", name, "class", otherClass.getLocation()));
    } else {
      ClusterChart otherCluster = st.informal.clusters.get(name);
      if (otherCluster != null) {
        problems.addProblem(new DuplicateClusterChartError(loc, otherCluster));
      } else {
        st.informal.clusters.put(name, node);
      }
    }
    
    for (ClassEntry entry : classes) {
      //TODO check for duplicate class entries
      st.informal.classClusterGraph.put(entry.getName(), node);
      st.informal.descriptionGraph.put(entry.getName(), entry.getDescription());
    }
    
    for (ClusterEntry entry : clusters) {
      //TODO check for duplicate cluster entries
      st.informal.classClusterGraph.put(entry.getName(), node);
      st.informal.descriptionGraph.put(entry.getName(), entry.getDescription());
    }

    indexing(node, indexing);
  }  

  public void visitAll(Collection<? extends AstNode> nodes) {
    if (nodes != null) {
      for (AstNode node : nodes) {
        node.accept(this);
      }
    }
  }
  
  public void visitNode(AstNode node) {
    if (node != null) {
      node.accept(this);
    }
  }
  
  @Override
  public void visitClientRelation(ClientRelation node, BONType client,
      BONType supplier, ClientEntityExpression clientEntities,
      TypeMark typeMark, String semanticLabel, SourceLocation loc) {
    
    st.clientRelations.add(node);
  }

  private void indexing(AstNode node, Indexing indexing) {
    if (indexing != null) {
      st.indexing.put(node, indexing);
    }
  }

}
