package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.AbstractVisitor;
import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BONType;
import ie.ucd.bon.ast.BinaryExp;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.BooleanConstant;
import ie.ucd.bon.ast.CallExp;
import ie.ucd.bon.ast.CharacterConstant;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClassEntry;
import ie.ucd.bon.ast.ClassInterface;
import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClientEntityExpression;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.ClusterEntry;
import ie.ucd.bon.ast.ContractClause;
import ie.ucd.bon.ast.Expression;
import ie.ucd.bon.ast.Feature;
import ie.ucd.bon.ast.FeatureArgument;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.HasType;
import ie.ucd.bon.ast.IVisitor;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.IntegerConstant;
import ie.ucd.bon.ast.KeywordConstant;
import ie.ucd.bon.ast.Quantification;
import ie.ucd.bon.ast.RealConstant;
import ie.ucd.bon.ast.RenameClause;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.ast.StaticComponent;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.ast.StaticRef;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.ast.TypeMark;
import ie.ucd.bon.ast.UnaryExp;
import ie.ucd.bon.ast.UnqualifiedCall;
import ie.ucd.bon.ast.VariableRange;
import ie.ucd.bon.ast.BinaryExp.Op;
import ie.ucd.bon.ast.Clazz.Mod;
import ie.ucd.bon.ast.FeatureSpecification.Modifier;
import ie.ucd.bon.ast.KeywordConstant.Constant;
import ie.ucd.bon.ast.Quantification.Quantifier;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.errors.ClassCannotHaveSelfAsParentError;
import ie.ucd.bon.typechecker.errors.DuplicateClassDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateClusterDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateFeatureDefinitionError;
import ie.ucd.bon.typechecker.errors.DuplicateFormalGenericNameError;
import ie.ucd.bon.typechecker.errors.DuplicateSystemDefinitionError;
import ie.ucd.bon.typechecker.errors.NameNotUniqueError;
import ie.ucd.bon.typechecker.informal.errors.DuplicateClassChartError;
import ie.ucd.bon.typechecker.informal.errors.DuplicateClusterChartError;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
  public void visitClazz(Clazz node, ClassName name, List<FormalGeneric> generics,
      Mod mod, ClassInterface classInterface, Boolean reused,
      Boolean persistent, Boolean interfaced, String comment, SourceLocation loc) {

    Clazz clazz = st.classes.get(name.getName());
    Cluster cluster = st.clusters.get(name.getName());

    if (cluster != null) {
      problems.addProblem(new NameNotUniqueError(loc, "Class", name.getName(), "cluster", cluster.getLocation()));  
    } else if (clazz != null) {
      problems.addProblem(new DuplicateClassDefinitionError(loc, clazz));
    } else {
      st.classes.put(name.getName(), node);

      if (!context.clusterStack.empty()) {
        st.classClusterGraph.put(name.getName(), context.clusterStack.peek());
      }
      
      Map<String,FormalGeneric> genericIdsMap = new HashMap<String,FormalGeneric>();
      for (FormalGeneric generic : generics) {
        FormalGeneric other = genericIdsMap.get(generic.getIdentifier());
        if (other == null) {
          genericIdsMap.put(generic.getIdentifier(), generic);
        } else {
          problems.addProblem(new DuplicateFormalGenericNameError(generic.getLocation(), generic.getIdentifier()));
        }
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
      List<Type> parents, List<Expression> invariant, Indexing indexing,
      SourceLocation loc) {
    
    for (Type parent : parents) {
      if (parent.getIdentifier().equals(context.clazz.getName().getName())) {
        problems.addProblem(new ClassCannotHaveSelfAsParentError(loc, context.clazz.getName().getName()));
      } else {
        st.classInheritanceGraph.put(context.clazz.getName().getName(), parent);
        st.simpleClassInheritanceGraph.put(context.clazz.getName().getName(), parent.getIdentifier());
      }
    }
    
    //TODO proper ST for feature
    visitAll(features);
    visitAll(invariant);

    indexing(context.clazz, indexing);
  }



  @Override
  public void visitFeature(Feature node,
      List<FeatureSpecification> featureSpecifications,
      List<ClassName> selectiveExport, String comment, SourceLocation loc) {

    context.selectiveExport = selectiveExport;
    visitAll(featureSpecifications);
  }
  
  @Override
  public void visitFeatureSpecification(FeatureSpecification node,
      Modifier modifier, List<String> featureNames,
      List<FeatureArgument> arguments, ContractClause contracts,
      HasType hasType, RenameClause renaming, String comment, SourceLocation loc) {

    for (String name : featureNames) {
      FeatureSpecification other = st.featuresMap.get(context.clazz, name);
      if (other == null) {
        st.featuresMap.put(context.clazz, name, node);
      } else {
        problems.addProblem(new DuplicateFeatureDefinitionError(loc, context.clazz.getName().getName(), name, other));
      }
    }
    
    st.selectiveExportMap.put(node, context.selectiveExport);
    
    visitNode(contracts);
  }

  @Override
  public void visitClassChart(ClassChart node, ClassName name,
      List<ClassName> inherits, List<String> queries, List<String> commands,
      List<String> constraints, Indexing indexing, String explanation,
      String part, SourceLocation loc) {
    
    //Check if name unique
    ClusterChart otherCluster = st.informal.clusters.get(name.getName());
    if (otherCluster != null) {
      problems.addProblem(new NameNotUniqueError(loc, "Cluster", name.getName(), "class", otherCluster.getLocation()));
    }else {
      ClassChart clazz = st.informal.classes.get(name.getName());
      if (clazz != null) {
        problems.addProblem(new DuplicateClassChartError(loc, clazz));  
      } else {
        st.informal.classes.put(name.getName(), node);
      }
    }

    for (ClassName parent : inherits) {
      if (parent.equals(name)) {
        problems.addProblem(new ClassCannotHaveSelfAsParentError(loc, name.getName()));
      } else {
        st.informal.classInheritanceGraph.put(node, parent.getName());      
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
        return;
      } else {
        st.informal.clusters.put(name, node);
      }
    }
    
    context.clusterChart = node;
    for (ClassEntry entry : classes) {
      //TODO check for duplicate class entries
      st.informal.classClusterGraph.put(entry.getName(), node);
      st.informal.descriptionGraph.put(entry.getName(), entry.getDescription());
    }
    for (ClusterEntry entry : clusters) {
      //TODO check for duplicate cluster entries
      st.informal.clusterClusterGraph.put(entry.getName(), node);
      st.informal.descriptionGraph.put(entry.getName(), entry.getDescription());
    }
    context.clusterChart = null;

    indexing(node, indexing);
  }  

  @Override
  public void visitClientRelation(ClientRelation node, StaticRef client,
      StaticRef supplier, ClientEntityExpression clientEntities,
      TypeMark typeMark, String semanticLabel, SourceLocation loc) {
    
    st.clientRelations.add(node);
  }

  @Override
  public void visitContractClause(ContractClause node,
      List<Expression> preconditions, List<Expression> postconditions,
      SourceLocation loc) {
    visitAll(preconditions);
    visitAll(postconditions);
  }

  @Override
  public void visitIntegerConstant(IntegerConstant node, Integer value,
      SourceLocation loc) {
    st.typeMap.put(node, BONType.mk("INTEGER"));
  }

  @Override
  public void visitKeywordConstant(KeywordConstant node, Constant constant,
      SourceLocation loc) {
    switch(constant) {
    case CURRENT:
      //TODO node has type of current class
      break;
    case RESULT:
      //TODO Check inside postcondition - done by typechecker
      break;
    case VOID:
      //TODO type void for this node
      break;
    }
  }

  @Override
  public void visitRealConstant(RealConstant node, Double value, SourceLocation loc) {
    st.typeMap.put(node, BONType.mk("REAL"));
  }

  @Override
  public void visitCharacterConstant(CharacterConstant node, Character value, SourceLocation loc) {
    st.typeMap.put(node, BONType.mk("CHARACTER"));
  }

  @Override
  public void visitQuantification(Quantification node, Quantifier quantifier,
      List<VariableRange> variableRanges, Expression restriction,
      Expression proposition, SourceLocation loc) {
    //TODO has type bool
  }

  @Override
  public void visitBooleanConstant(BooleanConstant node, Boolean value,
      SourceLocation loc) {
    st.typeMap.put(node, BONType.mk("BOOLEAN"));
  }

  @Override
  public void visitBinaryExp(BinaryExp node, Op op, Expression left,
      Expression right, SourceLocation loc) {
    visitNode(left);
    visitNode(right);
  
    switch(op) {
    case ADD:
    case POW:
    case SUB:
    case MUL:
      st.typeMap.put(node, arithmeticExpressionType(left, right));
      break;
      
    case DIV:
      st.typeMap.put(node, BONType.mk("REAL"));
      break;
    
    case MOD:
    case INTDIV:
      st.typeMap.put(node, BONType.mk("INTEGER"));
      break;
    
    case HASTYPE:
    case MEMBEROF:
    case NOTMEMBEROF:
      st.typeMap.put(node, BONType.mk("BOOLEAN"));
      break;
      
    case AND:
    case OR:
    case EQ:  
    case LE:
    case NEQ:
    case LT:
    case XOR:
    case GT:
    case GE:
    case EQUIV:
    case IMPLIES:
      st.typeMap.put(node, BONType.mk("BOOLEAN"));
      break;  
    }
    
  }
  
  private Type arithmeticExpressionType(Expression left, Expression right) {
    Type leftType = st.typeMap.get(left);
    Type rightType = st.typeMap.get(right);
    Type intType = BONType.mk("INTEGER");
    Type realType = BONType.mk("REAL");
    
    boolean isLeftInt = st.isSubtypeOrEqual(leftType, intType);
    boolean isRightInt = st.isSubtypeOrEqual(rightType, intType);
    boolean isLeftReal = st.isSubtypeOrEqual(leftType, realType);
    boolean isRightReal = st.isSubtypeOrEqual(rightType, realType);
    
    if (!(isLeftInt || isLeftReal) || !(isRightInt || isRightReal)) {
      //Typing error, will be picked up in type checker
      return null;
    } else {
      if (isLeftReal || isRightReal) {
        return realType;
      } else {
        return intType;
      }
    }
  }

  @Override
  public void visitUnaryExp(UnaryExp node, ie.ucd.bon.ast.UnaryExp.Op op,
      Expression expression, SourceLocation loc) {
    visitNode(expression);
  
    switch(op) {
    case ADD:
    case SUB:
      //It's the type contained within. Typechecker will report if it is not an INTEGER or REAL
      st.typeMap.put(node, st.typeMap.get(expression));
      break;
    case DELTA:
      //No type
      break;
    case OLD:
      st.typeMap.put(node, st.typeMap.get(expression));
      break;
    case NOT:  
      st.typeMap.put(node, BONType.mk("BOOLEAN"));
      break;
    }
  }
  
  @Override
  public void visitCallExp(CallExp node, Expression qualifier,
      List<UnqualifiedCall> callChain, SourceLocation loc) {
    visitNode(qualifier);
    
    if (qualifier == null) {
      context.callQualifier = BONType.mk(context.clazz.getName().getName());
    } else {
      context.callQualifier = st.typeMap.get(qualifier);
    }
    for (UnqualifiedCall call : callChain) {
      visitNode(call);
      context.callQualifier = st.typeMap.get(call);
    }
  }

  @Override
  public void visitUnqualifiedCall(UnqualifiedCall node, String id,
      List<Expression> args, SourceLocation loc) {
    //TODO, we need feature types in a previous pass...
    Type qualifier = context.callQualifier;
    //Type is the type of feature id for the qualifier type
  }

  private void indexing(AstNode node, Indexing indexing) {
    if (indexing != null) {
      st.indexing.put(node, indexing);
    }
  }
  
}

