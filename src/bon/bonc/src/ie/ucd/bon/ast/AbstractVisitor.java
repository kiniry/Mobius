
/** 
  This file is generated from abstract_visitor.tpl. Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public abstract class AbstractVisitor implements IVisitor {



  public void visitBinaryExp(BinaryExp node, BinaryExp.Op op, Expression left, Expression right, SourceLocation loc) {
    //Do nothing
  }

  public void visitBonSourceFile(BonSourceFile node, List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation loc) {
    //Do nothing
  }

  public void visitBooleanConstant(BooleanConstant node, Boolean value, SourceLocation loc) {
    //Do nothing
  }

  public void visitCallExp(CallExp node, Expression qualifier, List<UnqualifiedCall> callChain, SourceLocation loc) {
    //Do nothing
  }

  public void visitCharacterConstant(CharacterConstant node, Character value, SourceLocation loc) {
    //Do nothing
  }

  public void visitCharacterInterval(CharacterInterval node, Character start, Character stop, SourceLocation loc) {
    //Do nothing
  }

  public void visitClassChart(ClassChart node, String name, List<String> inherits, List<String> queries, List<String> commands, List<String> constraints, Indexing indexing, String explanation, String part, SourceLocation loc) {
    //Do nothing
  }

  public void visitClassDictionary(ClassDictionary node, String systemName, List<DictionaryEntry> entries, Indexing indexing, String explanation, String part, SourceLocation loc) {
    //Do nothing
  }

  public void visitClassEntry(ClassEntry node, String name, String description, SourceLocation loc) {
    //Do nothing
  }

  public void visitClassInterface(ClassInterface node, List<Feature> features, List<BONType> parents, List<Expression> invariant, Indexing indexing, SourceLocation loc) {
    //Do nothing
  }

  public void visitClassName(ClassName node, String name, SourceLocation loc) {
    //Do nothing
  }

  public void visitClazz(Clazz node, String name, List<FormalGeneric> generics, Clazz.Mod mod, ClassInterface classInterface, Boolean reused, Boolean persistent, Boolean interfaced, String comment, SourceLocation loc) {
    //Do nothing
  }

  public void visitClientEntityList(ClientEntityList node, List<ClientEntity> entities, SourceLocation loc) {
    //Do nothing
  }

  public void visitClientRelation(ClientRelation node, BONType client, BONType supplier, ClientEntityExpression clientEntities, TypeMark typeMark, String semanticLabel, SourceLocation loc) {
    //Do nothing
  }

  public void visitCluster(Cluster node, String name, List<StaticComponent> components, Boolean reused, String comment, SourceLocation loc) {
    //Do nothing
  }

  public void visitClusterChart(ClusterChart node, String name, Boolean isSystem, List<ClassEntry> classes, List<ClusterEntry> clusters, Indexing indexing, String explanation, String part, SourceLocation loc) {
    //Do nothing
  }

  public void visitClusterEntry(ClusterEntry node, String name, String description, SourceLocation loc) {
    //Do nothing
  }

  public void visitContractClause(ContractClause node, List<Expression> preconditions, List<Expression> postconditions, SourceLocation loc) {
    //Do nothing
  }

  public void visitCreationChart(CreationChart node, String name, List<CreationEntry> entries, Indexing indexing, String explanation, String part, SourceLocation loc) {
    //Do nothing
  }

  public void visitCreationEntry(CreationEntry node, String name, List<String> types, SourceLocation loc) {
    //Do nothing
  }

  public void visitDictionaryEntry(DictionaryEntry node, String name, List<String> clusters, String description, SourceLocation loc) {
    //Do nothing
  }

  public void visitDynamicDiagram(DynamicDiagram node, List<DynamicComponent> components, String extendedId, String comment, SourceLocation loc) {
    //Do nothing
  }

  public void visitEventChart(EventChart node, String systemName, Boolean incoming, Boolean outgoing, List<EventEntry> entries, Indexing indexing, String explanation, String part, SourceLocation loc) {
    //Do nothing
  }

  public void visitEventEntry(EventEntry node, String name, List<String> involved, SourceLocation loc) {
    //Do nothing
  }

  public void visitFeature(Feature node, List<FeatureSpecification> featureSpecifications, List<String> selectiveExport, String comment, SourceLocation loc) {
    //Do nothing
  }

  public void visitFeatureArgument(FeatureArgument node, String identifier, BONType type, SourceLocation loc) {
    //Do nothing
  }

  public void visitFeatureSpecification(FeatureSpecification node, FeatureSpecification.Modifier modifier, List<String> featureNames, List<FeatureArgument> arguments, ContractClause contracts, HasType hasType, RenameClause renaming, String comment, SourceLocation loc) {
    //Do nothing
  }

  public void visitFormalGeneric(FormalGeneric node, String identifier, BONType type, SourceLocation loc) {
    //Do nothing
  }

  public void visitGenericIndirection(GenericIndirection node, String indirectionElement, SourceLocation loc) {
    //Do nothing
  }

  public void visitHasType(HasType node, TypeMark mark, BONType type, SourceLocation loc) {
    //Do nothing
  }

  public void visitIndexClause(IndexClause node, String id, List<String> indexTerms, SourceLocation loc) {
    //Do nothing
  }

  public void visitIndexing(Indexing node, List<IndexClause> indexes, SourceLocation loc) {
    //Do nothing
  }

  public void visitIndirectionFeatureList(IndirectionFeatureList node, List<FeatureName> featureNames, SourceLocation loc) {
    //Do nothing
  }

  public void visitInheritanceRelation(InheritanceRelation node, BONType child, BONType parent, Multiplicity multiplicity, String semanticLabel, SourceLocation loc) {
    //Do nothing
  }

  public void visitIntegerConstant(IntegerConstant node, Integer value, SourceLocation loc) {
    //Do nothing
  }

  public void visitIntegerInterval(IntegerInterval node, Integer start, Integer stop, SourceLocation loc) {
    //Do nothing
  }

  public void visitKeywordConstant(KeywordConstant node, KeywordConstant.Constant constant, SourceLocation loc) {
    //Do nothing
  }

  public void visitLabelledAction(LabelledAction node, String label, String description, SourceLocation loc) {
    //Do nothing
  }

  public void visitMemberRange(MemberRange node, List<String> identifiers, Expression expression, SourceLocation loc) {
    //Do nothing
  }

  public void visitMultiplicity(Multiplicity node, Integer multiplicity, SourceLocation loc) {
    //Do nothing
  }

  public void visitNamedIndirection(NamedIndirection node, String className, List<IndirectionElement> indirectionElements, SourceLocation loc) {
    //Do nothing
  }

  public void visitObjectGroup(ObjectGroup node, ObjectGroup.Nameless nameless, String name, List<DynamicComponent> components, String comment, SourceLocation loc) {
    //Do nothing
  }

  public void visitObjectInstance(ObjectInstance node, ObjectName name, String comment, SourceLocation loc) {
    //Do nothing
  }

  public void visitObjectName(ObjectName node, String className, String extendedId, SourceLocation loc) {
    //Do nothing
  }

  public void visitObjectStack(ObjectStack node, ObjectName name, String comment, SourceLocation loc) {
    //Do nothing
  }

  public void visitParentIndirection(ParentIndirection node, GenericIndirection genericIndirection, SourceLocation loc) {
    //Do nothing
  }

  public void visitQuantification(Quantification node, Quantification.Quantifier quantifier, List<VariableRange> variableRanges, Expression restriction, Expression proposition, SourceLocation loc) {
    //Do nothing
  }

  public void visitRealConstant(RealConstant node, Double value, SourceLocation loc) {
    //Do nothing
  }

  public void visitRenameClause(RenameClause node, String className, String featureName, SourceLocation loc) {
    //Do nothing
  }

  public void visitScenarioChart(ScenarioChart node, String systemName, List<ScenarioEntry> entries, Indexing indexing, String explanation, String part, SourceLocation loc) {
    //Do nothing
  }

  public void visitScenarioDescription(ScenarioDescription node, String name, List<LabelledAction> actions, String comment, SourceLocation loc) {
    //Do nothing
  }

  public void visitScenarioEntry(ScenarioEntry node, String name, String description, SourceLocation loc) {
    //Do nothing
  }

  public void visitSetConstant(SetConstant node, List<EnumerationElement> enumerations, SourceLocation loc) {
    //Do nothing
  }

  public void visitStaticDiagram(StaticDiagram node, List<StaticComponent> components, String extendedId, String comment, SourceLocation loc) {
    //Do nothing
  }

  public void visitStringConstant(StringConstant node, String value, SourceLocation loc) {
    //Do nothing
  }

  public void visitSupplierIndirection(SupplierIndirection node, IndirectionFeaturePart indirectionFeaturePart, GenericIndirection genericIndirection, SourceLocation loc) {
    //Do nothing
  }

  public void visitType(Type node, String identifier, List<BONType> actualGenerics, String fullString, SourceLocation loc) {
    //Do nothing
  }

  public void visitTypeMark(TypeMark node, TypeMark.Mark mark, Integer multiplicity, SourceLocation loc) {
    //Do nothing
  }

  public void visitTypeRange(TypeRange node, List<String> identifiers, BONType type, SourceLocation loc) {
    //Do nothing
  }

  public void visitUnaryExp(UnaryExp node, UnaryExp.Op op, Expression expression, SourceLocation loc) {
    //Do nothing
  }

  public void visitUnqualifiedCall(UnqualifiedCall node, String id, List<Expression> args, SourceLocation loc) {
    //Do nothing
  }

}

