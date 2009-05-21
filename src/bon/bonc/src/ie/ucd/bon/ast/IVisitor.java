
/** 
  This file is generated from evaluator.tpl. Do not edit.
 */
package ie.ucd.bon.ast;

public interface IVisitor {



  void visitBinaryExp(BinaryExp node);

  void visitBonSourceFile(BonSourceFile node);

  void visitBooleanConstant(BooleanConstant node);

  void visitCallExp(CallExp node);

  void visitCharacterConstant(CharacterConstant node);

  void visitCharacterInterval(CharacterInterval node);

  void visitClassChart(ClassChart node);

  void visitClassDictionary(ClassDictionary node);

  void visitClassEntry(ClassEntry node);

  void visitClassInterface(ClassInterface node);

  void visitClassName(ClassName node);

  void visitClazz(Clazz node);

  void visitClientEntityList(ClientEntityList node);

  void visitClientRelation(ClientRelation node);

  void visitCluster(Cluster node);

  void visitClusterChart(ClusterChart node);

  void visitClusterEntry(ClusterEntry node);

  void visitContractClause(ContractClause node);

  void visitCreationChart(CreationChart node);

  void visitCreationEntry(CreationEntry node);

  void visitDictionaryEntry(DictionaryEntry node);

  void visitDynamicDiagram(DynamicDiagram node);

  void visitEventChart(EventChart node);

  void visitEventEntry(EventEntry node);

  void visitFeature(Feature node);

  void visitFeatureArgument(FeatureArgument node);

  void visitFeatureSpecification(FeatureSpecification node);

  void visitFormalGeneric(FormalGeneric node);

  void visitGenericIndirection(GenericIndirection node);

  void visitHasType(HasType node);

  void visitIndexClause(IndexClause node);

  void visitIndexing(Indexing node);

  void visitIndirectionFeatureList(IndirectionFeatureList node);

  void visitInheritanceRelation(InheritanceRelation node);

  void visitIntegerConstant(IntegerConstant node);

  void visitIntegerInterval(IntegerInterval node);

  void visitKeywordConstant(KeywordConstant node);

  void visitLabelledAction(LabelledAction node);

  void visitMemberRange(MemberRange node);

  void visitMultiplicity(Multiplicity node);

  void visitNamedIndirection(NamedIndirection node);

  void visitObjectGroup(ObjectGroup node);

  void visitObjectInstance(ObjectInstance node);

  void visitObjectName(ObjectName node);

  void visitObjectStack(ObjectStack node);

  void visitParentIndirection(ParentIndirection node);

  void visitQuantification(Quantification node);

  void visitRealConstant(RealConstant node);

  void visitRenameClause(RenameClause node);

  void visitScenarioChart(ScenarioChart node);

  void visitScenarioDescription(ScenarioDescription node);

  void visitScenarioEntry(ScenarioEntry node);

  void visitSetConstant(SetConstant node);

  void visitStaticDiagram(StaticDiagram node);

  void visitStringConstant(StringConstant node);

  void visitSupplierIndirection(SupplierIndirection node);

  void visitSystemChart(SystemChart node);

  void visitType(Type node);

  void visitTypeMark(TypeMark node);

  void visitTypeRange(TypeRange node);

  void visitUnaryExp(UnaryExp node);

  void visitUnqualifiedCall(UnqualifiedCall node);

}