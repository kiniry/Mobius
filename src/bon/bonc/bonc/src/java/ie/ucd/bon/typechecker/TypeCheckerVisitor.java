/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import static ie.ucd.bon.ast.FeatureSpecification.Modifier.DEFERRED;
import ie.ucd.bon.ast.AbstractVisitorWithAdditions;
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
import ie.ucd.bon.ast.FeatureName;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.HasType;
import ie.ucd.bon.ast.IVisitorWithAdditions;
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
import ie.ucd.bon.printer.PrettyPrintVisitor;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.errors.ClassCannotHaveSelfAsParentError;
import ie.ucd.bon.typechecker.errors.DeferredFeatureInNonDeferredClassError;
import ie.ucd.bon.typechecker.errors.InvalidClusterTypeError;
import ie.ucd.bon.typechecker.errors.InvalidFormalClassTypeError;
import ie.ucd.bon.typechecker.errors.InvalidStaticComponentTypeError;
import ie.ucd.bon.typechecker.errors.NoParentDeclaresFeatureError;
import ie.ucd.bon.typechecker.errors.NotContainedInClusterError;
import ie.ucd.bon.typechecker.errors.ParentFeatureIsDeferredError;
import ie.ucd.bon.typechecker.errors.ParentFeatureNotDeferredError;
import ie.ucd.bon.typechecker.informal.errors.InvalidInformalClassTypeError;
import ie.ucd.bon.util.HashMapStack;

import java.util.Collection;
import java.util.List;

public class TypeCheckerVisitor extends AbstractVisitorWithAdditions implements IVisitorWithAdditions {

  private final BONST st;
  private final VisitorContext context;
  private final Problems problems;
  private final HashMapStack<String,Type> tc;

  public TypeCheckerVisitor(BONST st) {
    this.st = st;
    this.problems = new Problems("TC");
    this.context = new VisitorContext();
    this.tc = new HashMapStack<String,Type>();
    
    initialiseTC();
  }
  
  private void initialiseTC() {
    tc.putAll(st.classNameToTypeMap); 
  }

  @Override
  public void visitBonSourceFile(BonSourceFile node, List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation loc) {
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
      problems.addProblem(new ClassCannotHaveSelfAsParentError(child.getReportingLocation(), child.getName().getName()));
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
          problems.addProblem(new InvalidClusterTypeError(current.getReportingLocation(), current.getName()));
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
    context.clazz = node;
    visitNode(classInterface);
    context.clazz = null;
  }

  @Override
  public void visitFeature(Feature node,
      List<FeatureSpecification> featureSpecifications,
      List<ClassName> selectiveExport, String comment, SourceLocation loc) {
    visitAll(featureSpecifications);
  }

  @Override
  public void visitFeatureSpecification(FeatureSpecification node,
      Modifier modifier, List<FeatureName> featureNames,
      List<FeatureArgument> arguments, ContractClause contracts,
      HasType hasType, RenameClause renaming, String comment, SourceLocation loc) {

    if (modifier == DEFERRED && context.clazz.getMod() != Clazz.Mod.DEFERRED) {
      problems.addProblem(new DeferredFeatureInNonDeferredClassError(loc, featureNames, context.clazz.getName().getName()));
    }

    for (FeatureName name : featureNames) {
      //TODO reference against table produced with Joe and Alex.
      switch(modifier) {
      case DEFERRED:
      case NONE:
        checkParentFeatureCompatible(node, name, false, false, false);
        break;
      case EFFECTIVE:
        checkParentFeatureCompatible(node, name, true, true, false);
        break;
      case REDEFINED:
        checkParentFeatureCompatible(node, name, true, false, true);
        break;
      }
    }

    visitNode(contracts);
  }

  private void checkParentFeatureCompatible(FeatureSpecification node, FeatureName featureNameNode, boolean parentFeatureMustExist,
      boolean parentFeatureMustBeDeferred, boolean parentFeatureMustBeNonDeferred) {
    String className = context.clazz.getName().getName();
    String featureName = featureNameNode.getName();
    
    FeatureSpecification parentFeature = findParentFeatureWithName(className, featureName);

    if (parentFeature == null) {
      if (parentFeatureMustExist) {
        problems.addProblem(new NoParentDeclaresFeatureError(featureNameNode.getLocation(), featureName, className, PrettyPrintVisitor.toString(node.getModifier())));
      }
    } else {
      if (parentFeatureMustBeDeferred && parentFeature.getModifier() != DEFERRED) {
        problems.addProblem(new ParentFeatureNotDeferredError(featureNameNode.getLocation(), featureName, st.featureDeclaringClassMap.get(node).name.name));
      }

      if (parentFeatureMustBeNonDeferred && parentFeature.getModifier() == DEFERRED) {
        problems.addProblem(new ParentFeatureIsDeferredError(featureNameNode.getLocation(), featureName, st.featureDeclaringClassMap.get(node).name.name));
      }

      //TODO check return type and arguments are type-compatible
    }
  }

  private FeatureSpecification findParentFeatureWithName(String className, String featureName) {
    Collection<String> parents = st.simpleClassInheritanceGraph.get(className);
    //TODO handle renamings
    for (String parent : parents) {
      Clazz parentClass = st.classes.get(parent);
      if (parentClass != null) {
        //Look for feature for this class
        FeatureSpecification featureSpec = st.featuresMap.get(parentClass, featureName);
        if (featureSpec != null) {
          return featureSpec;
        }
        //Look in parent classes
        featureSpec = findParentFeatureWithName(parent, featureName);
        if (featureSpec != null) {
          return featureSpec;
        }
      }
    }

    //No such feature
    return null;
  }

  @Override
  public void visitCluster(Cluster node, String name, List<StaticComponent> components, Boolean reused, String comment, SourceLocation loc) {
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
    Collection<Cluster> clusters = st.classClusterMap.get(className);
    for (Cluster cluster : clusters) {
      if (cluster.name.equals(clusterName)) {
        return true;
      }
    }
    return false;
  }

  private boolean isClusterInCluster(String containee, String containing) {
    return st.clusterClusterGraph.containsEntry(containee, st.clusters.get(containing));
  }



  @Override
  public void visitContractClause(ContractClause node,
      List<Expression> preconditions, List<Expression> postconditions,
      SourceLocation loc) {
    visitAll(preconditions);
    visitAll(postconditions);
  }

  /*
  @Override
  public void visitIntegerConstant(IntegerConstant node, Integer value,
      SourceLocation loc) {
    st.typeMap.put(node, BONType.mk("INTEGER"));
  }



  @Override
  public void visitKeywordConstant(KeywordConstant node,
      ie.ucd.bon.ast.KeywordConstant.Constant constant, SourceLocation loc) {
    switch(constant) {
    case CURRENT:
      st.typeMap.put(node, BONType.mk(context.clazz.getName().getName()));
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
      //TODO Typing error
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
      compareType(new Type[] {BONType.mk("REAL"), BONType.mk("INTEGER")}, st.typeMap.get(expression), loc, "");
      st.typeMap.put(node, st.typeMap.get(expression));
      break;
    case DELTA:
      //No type
      //TODO check within has valid type
      break;
    case OLD:
      st.typeMap.put(node, st.typeMap.get(expression));
      break;
    case NOT:
      Type boolType = BONType.mk("BOOLEAN");
      compareType(boolType, st.typeMap.get(expression), loc, "Operator 'not' can only be applied to boolean expressions. ");
      st.typeMap.put(node, boolType);
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
    //Type qualifier = context.callQualifier;

    visitAll(args);
    //Type is the type of feature id for the qualifier type

  }

  private boolean compareType(Type expected, Type found, SourceLocation loc, String explanation) {
    if (found == null) {
      //TODO uncomment the addProblem calls in the two compareType methods
      //problems.addProblem(new TypeMismatchWithExplanationError(loc, explanation, typeToString(expected), null));
      return false;
    } else if (!st.isSubtypeOrEqual(found, expected)) {
      //problems.addProblem(new TypeMismatchWithExplanationError(loc, explanation, typeToString(expected), typeToString(found)));
      return false;
    } else {
      return true;
    }
  }

  private boolean compareType(Type[] expected, Type found, SourceLocation loc, String explanation) {
    if (found == null) {
      //problems.addProblem(new TypeMismatchWithExplanationError(loc, explanation, typeChoices(expected), null));
      return false;
    } else {
      for (Type type : expected) {
        if (st.isSubtypeOrEqual(found, type)) {
          return true;
        }
      }
      //problems.addProblem(new TypeMismatchWithExplanationError(loc, explanation, typeChoices(expected), typeToString(found)));
      return false;
    }
  }
*/
  private String typeChoices(Type[] types) {
    if (types.length == 0) {
      return "";
    } else if (types.length == 1) {
      return typeToString(types[0]);
    } else {
      StringBuilder sb = new StringBuilder();
      for (int i=0; i < types.length-2; i++) {
        sb.append(typeToString(types[i]));
        sb.append(", ");
      }
      sb.append(" or ");
      sb.append(typeToString(types[types.length-1]));
      return sb.toString();
    }
  }

  private String typeToString(Type type) {
    //TODO fix
    return type.getIdentifier();
  }

  public Problems getProblems() {
    return problems;
  }
}
