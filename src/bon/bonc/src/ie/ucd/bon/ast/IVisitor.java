
/** 
  This file is generated from abstract_visitor.tpl. Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;

public interface IVisitor {



  void visitBinaryExp(BinaryExp node, BinaryExp.Op op , Expression left , Expression right );

  void visitBonSourceFile(BonSourceFile node, List<SpecificationElement> bonSpecification , Indexing indexing );

  void visitBooleanConstant(BooleanConstant node, Boolean value );

  void visitCallExp(CallExp node, Expression qualifier , List<UnqualifiedCall> callChain );

  void visitCharacterConstant(CharacterConstant node, Character value );

  void visitCharacterInterval(CharacterInterval node, Character start , Character stop );

  void visitClassChart(ClassChart node, String name , List<String> inherits , List<String> queries , List<String> commands , List<String> constraints , Indexing indexing , String explanation , String part );

  void visitClassDictionary(ClassDictionary node, String systemName , List<DictionaryEntry> entries , Indexing indexing , String explanation , String part );

  void visitClassEntry(ClassEntry node, String name , String description );

  void visitClassInterface(ClassInterface node, List<Feature> features , List<BONType> parents , List<Expression> invariant , Indexing indexing );

  void visitClassName(ClassName node, String name );

  void visitClazz(Clazz node, String name , List<FormalGeneric> generics , Clazz.Mod mod , ClassInterface classInterface , Boolean reused , Boolean persistent , Boolean interfaced , String comment );

  void visitClientEntityList(ClientEntityList node, List<ClientEntity> entities );

  void visitClientRelation(ClientRelation node, BONType client , BONType supplier , ClientEntityExpression clientEntities , TypeMark typeMark , String semanticLabel );

  void visitCluster(Cluster node, String name , List<StaticComponent> components , Boolean reused , String comment );

  void visitClusterChart(ClusterChart node, String name , List<ClassEntry> classes , List<ClusterEntry> clusters , Indexing indexing , String explanation , String part );

  void visitClusterEntry(ClusterEntry node, String name , String description );

  void visitContractClause(ContractClause node, List<Expression> preconditions , List<Expression> postconditions );

  void visitCreationChart(CreationChart node, String name , List<CreationEntry> entries , Indexing indexing , String explanation , String part );

  void visitCreationEntry(CreationEntry node, String name , List<String> types );

  void visitDictionaryEntry(DictionaryEntry node, String name , List<String> clusters , String description );

  void visitDynamicDiagram(DynamicDiagram node, List<DynamicComponent> components , String extendedId , String comment );

  void visitEventChart(EventChart node, String systemName , Boolean incoming , Boolean outgoing , List<EventEntry> entries , Indexing indexing , String explanation , String part );

  void visitEventEntry(EventEntry node, String name , List<String> involved );

  void visitFeature(Feature node, List<FeatureSpecification> featureSpecifications , List<String> selectiveExport , String comment );

  void visitFeatureArgument(FeatureArgument node, String identifier , BONType type );

  void visitFeatureSpecification(FeatureSpecification node, FeatureSpecification.Modifier modifier , List<String> featureNames , List<FeatureArgument> arguments , ContractClause contracts , HasType hasType , RenameClause renaming , String comment );

  void visitFormalGeneric(FormalGeneric node, String identifier , BONType type );

  void visitGenericIndirection(GenericIndirection node, String indirectionElement );

  void visitHasType(HasType node, TypeMark mark , BONType type );

  void visitIndexClause(IndexClause node, String id , List<String> indexTerms );

  void visitIndexing(Indexing node, List<IndexClause> indexes );

  void visitIndirectionFeatureList(IndirectionFeatureList node, List<FeatureName> featureNames );

  void visitInheritanceRelation(InheritanceRelation node, BONType child , BONType parent , Multiplicity multiplicity , String semanticLabel );

  void visitIntegerConstant(IntegerConstant node, Integer value );

  void visitIntegerInterval(IntegerInterval node, Integer start , Integer stop );

  void visitKeywordConstant(KeywordConstant node, KeywordConstant.Constant constant );

  void visitLabelledAction(LabelledAction node, String label , String description );

  void visitMemberRange(MemberRange node, List<String> identifiers , Expression expression );

  void visitMultiplicity(Multiplicity node, Integer multiplicity );

  void visitNamedIndirection(NamedIndirection node, String className , List<IndirectionElement> indirectionElements );

  void visitObjectGroup(ObjectGroup node, ObjectGroup.Nameless nameless , String name , List<DynamicComponent> components , String comment );

  void visitObjectInstance(ObjectInstance node, ObjectName name , String comment );

  void visitObjectName(ObjectName node, String className , String extendedId );

  void visitObjectStack(ObjectStack node, ObjectName name , String comment );

  void visitParentIndirection(ParentIndirection node, GenericIndirection genericIndirection );

  void visitQuantification(Quantification node, Quantification.Quantifier quantifier , List<VariableRange> variableRanges , Expression restriction , Expression proposition );

  void visitRealConstant(RealConstant node, Double value );

  void visitRenameClause(RenameClause node, String className , String featureName );

  void visitScenarioChart(ScenarioChart node, String systemName , List<ScenarioEntry> entries , Indexing indexing , String explanation , String part );

  void visitScenarioDescription(ScenarioDescription node, String name , List<LabelledAction> actions , String comment );

  void visitScenarioEntry(ScenarioEntry node, String name , String description );

  void visitSetConstant(SetConstant node, List<EnumerationElement> enumerations );

  void visitStaticDiagram(StaticDiagram node, List<StaticComponent> components , String extendedId , String comment );

  void visitStringConstant(StringConstant node, String value );

  void visitSupplierIndirection(SupplierIndirection node, IndirectionFeaturePart indirectionFeaturePart , GenericIndirection genericIndirection );

  void visitSystemChart(SystemChart node, String name , List<ClusterEntry> clusters , Indexing indexing , String explanation , String part );

  void visitType(Type node, String identifier , List<BONType> actualGenerics , String fullString );

  void visitTypeMark(TypeMark node, TypeMark.Mark mark , Integer multiplicity );

  void visitTypeRange(TypeRange node, List<String> identifiers , BONType type );

  void visitUnaryExp(UnaryExp node, UnaryExp.Op op , Expression expression );

  void visitUnqualifiedCall(UnqualifiedCall node, String id , List<Expression> args );

}