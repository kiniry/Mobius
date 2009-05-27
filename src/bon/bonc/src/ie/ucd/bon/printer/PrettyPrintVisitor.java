package ie.ucd.bon.printer;

import ie.ucd.bon.ast.AbstractVisitor;
import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BONType;
import ie.ucd.bon.ast.BinaryExp;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.BooleanConstant;
import ie.ucd.bon.ast.CallExp;
import ie.ucd.bon.ast.CharacterConstant;
import ie.ucd.bon.ast.CharacterInterval;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClassDictionary;
import ie.ucd.bon.ast.ClassEntry;
import ie.ucd.bon.ast.ClassInterface;
import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClientEntity;
import ie.ucd.bon.ast.ClientEntityExpression;
import ie.ucd.bon.ast.ClientEntityList;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.ClusterEntry;
import ie.ucd.bon.ast.ContractClause;
import ie.ucd.bon.ast.CreationChart;
import ie.ucd.bon.ast.CreationEntry;
import ie.ucd.bon.ast.DictionaryEntry;
import ie.ucd.bon.ast.DynamicComponent;
import ie.ucd.bon.ast.DynamicDiagram;
import ie.ucd.bon.ast.EnumerationElement;
import ie.ucd.bon.ast.EventChart;
import ie.ucd.bon.ast.EventEntry;
import ie.ucd.bon.ast.Expression;
import ie.ucd.bon.ast.Feature;
import ie.ucd.bon.ast.FeatureArgument;
import ie.ucd.bon.ast.FeatureName;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.GenericIndirection;
import ie.ucd.bon.ast.HasType;
import ie.ucd.bon.ast.IVisitor;
import ie.ucd.bon.ast.IndexClause;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.IndirectionElement;
import ie.ucd.bon.ast.IndirectionFeatureList;
import ie.ucd.bon.ast.IndirectionFeaturePart;
import ie.ucd.bon.ast.InheritanceRelation;
import ie.ucd.bon.ast.IntegerConstant;
import ie.ucd.bon.ast.IntegerInterval;
import ie.ucd.bon.ast.KeywordConstant;
import ie.ucd.bon.ast.LabelledAction;
import ie.ucd.bon.ast.MemberRange;
import ie.ucd.bon.ast.Multiplicity;
import ie.ucd.bon.ast.NamedIndirection;
import ie.ucd.bon.ast.ObjectGroup;
import ie.ucd.bon.ast.ObjectInstance;
import ie.ucd.bon.ast.ObjectName;
import ie.ucd.bon.ast.ObjectStack;
import ie.ucd.bon.ast.ParentIndirection;
import ie.ucd.bon.ast.Quantification;
import ie.ucd.bon.ast.RealConstant;
import ie.ucd.bon.ast.RenameClause;
import ie.ucd.bon.ast.ScenarioChart;
import ie.ucd.bon.ast.ScenarioDescription;
import ie.ucd.bon.ast.ScenarioEntry;
import ie.ucd.bon.ast.SetConstant;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.ast.StaticComponent;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.ast.StringConstant;
import ie.ucd.bon.ast.SupplierIndirection;
import ie.ucd.bon.ast.SystemChart;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.ast.TypeMark;
import ie.ucd.bon.ast.TypeRange;
import ie.ucd.bon.ast.UnaryExp;
import ie.ucd.bon.ast.UnqualifiedCall;
import ie.ucd.bon.ast.VariableRange;
import ie.ucd.bon.ast.BinaryExp.Op;
import ie.ucd.bon.ast.Clazz.Mod;
import ie.ucd.bon.ast.FeatureSpecification.Modifier;
import ie.ucd.bon.ast.KeywordConstant.Constant;
import ie.ucd.bon.ast.ObjectGroup.Nameless;
import ie.ucd.bon.ast.Quantification.Quantifier;
import ie.ucd.bon.ast.TypeMark.Mark;

import java.io.PrintStream;
import java.util.List;

public class PrettyPrintVisitor extends AbstractVisitor implements IVisitor {

  private final TextPrinter tp;
  
  public PrettyPrintVisitor(PrintStream ps) {
    tp = new TextPrinter(ps);
  }

  @Override
  public void visitBinaryExp(BinaryExp node, Op op, Expression left,
      Expression right) {
    // TODO Auto-generated method stub
    super.visitBinaryExp(node, op, left, right);
  }

  @Override
  public void visitBonSourceFile(BonSourceFile node,
      List<SpecificationElement> bonSpecification, Indexing indexing) {
    if (indexing != null) {
      indexing.accept(this);
      tp.printLine();
    }
    for (SpecificationElement spec : bonSpecification) {
      spec.accept(this);
    }
  }

  @Override
  public void visitBooleanConstant(BooleanConstant node, Boolean value) {
    tp.print(value.toString());
  }

  @Override
  public void visitCallExp(CallExp node, Expression qualifier,
      List<UnqualifiedCall> callChain) {
    // TODO Auto-generated method stub
    super.visitCallExp(node, qualifier, callChain);
  }

  @Override
  public void visitCharacterConstant(CharacterConstant node, Character value) {
    // TODO Auto-generated method stub
    super.visitCharacterConstant(node, value);
  }

  @Override
  public void visitCharacterInterval(CharacterInterval node, Character start,
      Character stop) {
    // TODO Auto-generated method stub
    super.visitCharacterInterval(node, start, stop);
  }

  @Override
  public void visitClassChart(ClassChart node, String name,
      List<String> inherits, List<String> queries, List<String> commands,
      List<String> constraints, Indexing indexing, String explanation,
      String part) {
    // TODO Auto-generated method stub
    super.visitClassChart(node, name, inherits, queries, commands, constraints,
        indexing, explanation, part);
  }

  @Override
  public void visitClassDictionary(ClassDictionary node, String systemName,
      List<DictionaryEntry> entries, Indexing indexing, String explanation,
      String part) {
    // TODO Auto-generated method stub
    super.visitClassDictionary(node, systemName, entries, indexing, explanation,
        part);
  }

  @Override
  public void visitClassEntry(ClassEntry node, String name, String description) {
    // TODO Auto-generated method stub
    super.visitClassEntry(node, name, description);
  }

  @Override
  public void visitClassInterface(ClassInterface node, List<Feature> features,
      List<BONType> parents, List<Expression> invariant, Indexing indexing) {
    // TODO Auto-generated method stub
    super.visitClassInterface(node, features, parents, invariant, indexing);
  }

  @Override
  public void visitClassName(ClassName node, String name) {
    tp.print(name);
  }

  @Override
  public void visitClazz(Clazz node, String name, List<FormalGeneric> generics,
      Mod mod, ClassInterface classInterface, Boolean reused,
      Boolean persistent, Boolean interfaced, String comment) {
    tp.print(toString(mod));
    tp.print(name);
    
    if (generics != null && generics.size() > 0) {
      //TODO print list of...
    } else {
      tp.print(" ");
    }
    if (reused) {
      tp.print("reused ");
    }
    if (persistent) {
      tp.print("persistent ");
    }
    if (interfaced) {
      tp.print("interfaced ");
    }
    tp.printLine();
    printComment(comment);
    visitNodeIfNonNull(classInterface);
  }

  @Override
  public void visitClientEntityList(ClientEntityList node,
      List<ClientEntity> entities) {
    // TODO Auto-generated method stub
    super.visitClientEntityList(node, entities);
  }

  @Override
  public void visitClientRelation(ClientRelation node, BONType client,
      BONType supplier, ClientEntityExpression clientEntities,
      TypeMark typeMark, String semanticLabel) {
    // TODO Auto-generated method stub
    super.visitClientRelation(node, client, supplier, clientEntities, typeMark,
        semanticLabel);
  }

  @Override
  public void visitCluster(Cluster node, String name,
      List<StaticComponent> components, Boolean reused, String comment) {
    // TODO Auto-generated method stub
    super.visitCluster(node, name, components, reused, comment);
  }

  @Override
  public void visitClusterChart(ClusterChart node, String name,
      List<ClassEntry> classes, List<ClusterEntry> clusters, Indexing indexing,
      String explanation, String part) {
    // TODO Auto-generated method stub
    super.visitClusterChart(node, name, classes, clusters, indexing, explanation,
        part);
  }

  @Override
  public void visitClusterEntry(ClusterEntry node, String name,
      String description) {
    // TODO Auto-generated method stub
    super.visitClusterEntry(node, name, description);
  }

  @Override
  public void visitContractClause(ContractClause node,
      List<Expression> preconditions, List<Expression> postconditions) {
    // TODO Auto-generated method stub
    super.visitContractClause(node, preconditions, postconditions);
  }

  @Override
  public void visitCreationChart(CreationChart node, String name,
      List<CreationEntry> entries, Indexing indexing, String explanation,
      String part) {
    // TODO Auto-generated method stub
    super.visitCreationChart(node, name, entries, indexing, explanation, part);
  }

  @Override
  public void visitCreationEntry(CreationEntry node, String name,
      List<String> types) {
    // TODO Auto-generated method stub
    super.visitCreationEntry(node, name, types);
  }

  @Override
  public void visitDictionaryEntry(DictionaryEntry node, String name,
      List<String> clusters, String description) {
    // TODO Auto-generated method stub
    super.visitDictionaryEntry(node, name, clusters, description);
  }

  @Override
  public void visitDynamicDiagram(DynamicDiagram node,
      List<DynamicComponent> components, String extendedId, String comment) {
    // TODO Auto-generated method stub
    super.visitDynamicDiagram(node, components, extendedId, comment);
  }

  @Override
  public void visitEventChart(EventChart node, String systemName,
      Boolean incoming, Boolean outgoing, List<EventEntry> entries,
      Indexing indexing, String explanation, String part) {
    // TODO Auto-generated method stub
    super.visitEventChart(node, systemName, incoming, outgoing, entries, indexing,
        explanation, part);
  }

  @Override
  public void visitEventEntry(EventEntry node, String name,
      List<String> involved) {
    // TODO Auto-generated method stub
    super.visitEventEntry(node, name, involved);
  }

  @Override
  public void visitFeature(Feature node,
      List<FeatureSpecification> featureSpecifications,
      List<String> selectiveExport, String comment) {
    // TODO Auto-generated method stub
    super.visitFeature(node, featureSpecifications, selectiveExport, comment);
  }

  @Override
  public void visitFeatureArgument(FeatureArgument node, String identifier,
      BONType type) {
    // TODO Auto-generated method stub
    super.visitFeatureArgument(node, identifier, type);
  }

  @Override
  public void visitFeatureSpecification(FeatureSpecification node,
      Modifier modifier, List<String> featureNames,
      List<FeatureArgument> arguments, ContractClause contracts,
      HasType hasType, RenameClause renaming, String comment) {
    // TODO Auto-generated method stub
    super.visitFeatureSpecification(node, modifier, featureNames, arguments,
        contracts, hasType, renaming, comment);
  }

  @Override
  public void visitFormalGeneric(FormalGeneric node, String identifier,
      BONType type) {
    // TODO Auto-generated method stub
    super.visitFormalGeneric(node, identifier, type);
  }

  @Override
  public void visitGenericIndirection(GenericIndirection node,
      String indirectionElement) {
    // TODO Auto-generated method stub
    super.visitGenericIndirection(node, indirectionElement);
  }

  @Override
  public void visitHasType(HasType node, TypeMark mark, BONType type) {
    // TODO Auto-generated method stub
    super.visitHasType(node, mark, type);
  }

  @Override
  public void visitIndexClause(IndexClause node, String id,
      List<String> indexTerms) {
    // TODO Auto-generated method stub
    super.visitIndexClause(node, id, indexTerms);
  }

  @Override
  public void visitIndexing(Indexing node, List<IndexClause> indexes) {
    for (IndexClause clause : indexes) {
      clause.accept(this);
      tp.printLine();
    }
  }

  @Override
  public void visitIndirectionFeatureList(IndirectionFeatureList node,
      List<FeatureName> featureNames) {
    // TODO Auto-generated method stub
    super.visitIndirectionFeatureList(node, featureNames);
  }

  @Override
  public void visitInheritanceRelation(InheritanceRelation node, BONType child,
      BONType parent, Multiplicity multiplicity, String semanticLabel) {
    // TODO Auto-generated method stub
    super
        .visitInheritanceRelation(node, child, parent, multiplicity, semanticLabel);
  }

  @Override
  public void visitIntegerConstant(IntegerConstant node, Integer value) {
    // TODO Auto-generated method stub
    super.visitIntegerConstant(node, value);
  }

  @Override
  public void visitIntegerInterval(IntegerInterval node, Integer start,
      Integer stop) {
    // TODO Auto-generated method stub
    super.visitIntegerInterval(node, start, stop);
  }

  @Override
  public void visitKeywordConstant(KeywordConstant node, Constant constant) {
    // TODO Auto-generated method stub
    super.visitKeywordConstant(node, constant);
  }

  @Override
  public void visitLabelledAction(LabelledAction node, String label,
      String description) {
    // TODO Auto-generated method stub
    super.visitLabelledAction(node, label, description);
  }

  @Override
  public void visitMemberRange(MemberRange node, List<String> identifiers,
      Expression expression) {
    // TODO Auto-generated method stub
    super.visitMemberRange(node, identifiers, expression);
  }

  @Override
  public void visitMultiplicity(Multiplicity node, Integer multiplicity) {
    // TODO Auto-generated method stub
    super.visitMultiplicity(node, multiplicity);
  }

  @Override
  public void visitNamedIndirection(NamedIndirection node, String className,
      List<IndirectionElement> indirectionElements) {
    // TODO Auto-generated method stub
    super.visitNamedIndirection(node, className, indirectionElements);
  }

  @Override
  public void visitObjectGroup(ObjectGroup node, Nameless nameless,
      String name, List<DynamicComponent> components, String comment) {
    // TODO Auto-generated method stub
    super.visitObjectGroup(node, nameless, name, components, comment);
  }

  @Override
  public void visitObjectInstance(ObjectInstance node, ObjectName name,
      String comment) {
    // TODO Auto-generated method stub
    super.visitObjectInstance(node, name, comment);
  }

  @Override
  public void visitObjectName(ObjectName node, String className,
      String extendedId) {
    // TODO Auto-generated method stub
    super.visitObjectName(node, className, extendedId);
  }

  @Override
  public void visitObjectStack(ObjectStack node, ObjectName name, String comment) {
    // TODO Auto-generated method stub
    super.visitObjectStack(node, name, comment);
  }

  @Override
  public void visitParentIndirection(ParentIndirection node,
      GenericIndirection genericIndirection) {
    // TODO Auto-generated method stub
    super.visitParentIndirection(node, genericIndirection);
  }

  @Override
  public void visitQuantification(Quantification node, Quantifier quantifier,
      List<VariableRange> variableRanges, Expression restriction,
      Expression proposition) {
    // TODO Auto-generated method stub
    super.visitQuantification(node, quantifier, variableRanges, restriction,
        proposition);
  }

  @Override
  public void visitRealConstant(RealConstant node, Double value) {
    // TODO Auto-generated method stub
    super.visitRealConstant(node, value);
  }

  @Override
  public void visitRenameClause(RenameClause node, String className,
      String featureName) {
    // TODO Auto-generated method stub
    super.visitRenameClause(node, className, featureName);
  }

  @Override
  public void visitScenarioChart(ScenarioChart node, String systemName,
      List<ScenarioEntry> entries, Indexing indexing, String explanation,
      String part) {
    // TODO Auto-generated method stub
    super
        .visitScenarioChart(node, systemName, entries, indexing, explanation, part);
  }

  @Override
  public void visitScenarioDescription(ScenarioDescription node, String name,
      List<LabelledAction> actions, String comment) {
    // TODO Auto-generated method stub
    super.visitScenarioDescription(node, name, actions, comment);
  }

  @Override
  public void visitScenarioEntry(ScenarioEntry node, String name,
      String description) {
    // TODO Auto-generated method stub
    super.visitScenarioEntry(node, name, description);
  }

  @Override
  public void visitSetConstant(SetConstant node,
      List<EnumerationElement> enumerations) {
    // TODO Auto-generated method stub
    super.visitSetConstant(node, enumerations);
  }

  @Override
  public void visitStaticDiagram(StaticDiagram node,
      List<StaticComponent> components, String extendedId, String comment) {
    // TODO Auto-generated method stub
    super.visitStaticDiagram(node, components, extendedId, comment);
  }

  @Override
  public void visitStringConstant(StringConstant node, String value) {
    // TODO Auto-generated method stub
    super.visitStringConstant(node, value);
  }

  @Override
  public void visitSupplierIndirection(SupplierIndirection node,
      IndirectionFeaturePart indirectionFeaturePart,
      GenericIndirection genericIndirection) {
    // TODO Auto-generated method stub
    super
        .visitSupplierIndirection(node, indirectionFeaturePart, genericIndirection);
  }

  @Override
  public void visitSystemChart(SystemChart node, String name,
      List<ClusterEntry> clusters, Indexing indexing, String explanation,
      String part) {
    // TODO Auto-generated method stub
    super.visitSystemChart(node, name, clusters, indexing, explanation, part);
  }

  @Override
  public void visitType(Type node, String identifier,
      List<BONType> actualGenerics, String fullString) {
    // TODO Auto-generated method stub
    super.visitType(node, identifier, actualGenerics, fullString);
  }

  @Override
  public void visitTypeMark(TypeMark node, Mark mark, Integer multiplicity) {
    // TODO Auto-generated method stub
    super.visitTypeMark(node, mark, multiplicity);
  }

  @Override
  public void visitTypeRange(TypeRange node, List<String> identifiers,
      BONType type) {
    // TODO Auto-generated method stub
    super.visitTypeRange(node, identifiers, type);
  }

  @Override
  public void visitUnaryExp(UnaryExp node, ie.ucd.bon.ast.UnaryExp.Op op,
      Expression expression) {
    // TODO Auto-generated method stub
    super.visitUnaryExp(node, op, expression);
  }

  @Override
  public void visitUnqualifiedCall(UnqualifiedCall node, String id,
      List<Expression> args) {
    // TODO Auto-generated method stub
    super.visitUnqualifiedCall(node, id, args);
  }
  
  
  protected String toString(KeywordConstant.Constant constant) {
    switch (constant) {
    case CURRENT:
      return "Current";
    case VOID:
      return "Void";
    }
    return "";
  }
  
  protected String toString(Clazz.Mod modifier) {
    switch (modifier) {
    case DEFERRED:
      return "deferred ";
    case EFFECTIVE:
      return "effective ";
    case ROOT:
      return "root ";
    default:
      return "";
    }
  }
  
  protected void printComment(String commentText) {
    if (commentText != null) {
      tp.printLine("--" + commentText);
    }
  }
  
  protected final void visitNodeIfNonNull(AstNode node) {
    if (node != null) {
      node.accept(this);
    }
  }
}
