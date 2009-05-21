package ie.ucd.bon.printer;

import ie.ucd.bon.ast.AbstractVisitor;
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
import ie.ucd.bon.ast.ClientEntityList;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.ClusterEntry;
import ie.ucd.bon.ast.ContractClause;
import ie.ucd.bon.ast.CreationChart;
import ie.ucd.bon.ast.CreationEntry;
import ie.ucd.bon.ast.DictionaryEntry;
import ie.ucd.bon.ast.DynamicDiagram;
import ie.ucd.bon.ast.EventChart;
import ie.ucd.bon.ast.EventEntry;
import ie.ucd.bon.ast.Feature;
import ie.ucd.bon.ast.FeatureArgument;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.GenericIndirection;
import ie.ucd.bon.ast.HasType;
import ie.ucd.bon.ast.IVisitor;
import ie.ucd.bon.ast.IndexClause;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.IndirectionFeatureList;
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
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.ast.StringConstant;
import ie.ucd.bon.ast.SupplierIndirection;
import ie.ucd.bon.ast.SystemChart;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.ast.TypeMark;
import ie.ucd.bon.ast.TypeRange;
import ie.ucd.bon.ast.UnaryExp;
import ie.ucd.bon.ast.UnqualifiedCall;

import java.io.PrintStream;

public class PrettyPrintVisitor extends AbstractVisitor implements IVisitor {

  private final TextPrinter tp;
  
  public PrettyPrintVisitor(PrintStream ps) {
    tp = new TextPrinter(ps);
  }
  
  @Override
  public void visitBinaryExp(BinaryExp node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitBonSourceFile(BonSourceFile node) {
    Indexing indexing = node.getIndexing();
    if (indexing != null) {
      indexing.accept(this);
      tp.printLine();
    }
    for (SpecificationElement spec : node.getBonSpecification()) {
      spec.accept(this);
    }
  }

  @Override
  public void visitBooleanConstant(BooleanConstant node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitCallExp(CallExp node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitCharacterConstant(CharacterConstant node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitCharacterInterval(CharacterInterval node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitClassChart(ClassChart node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitClassDictionary(ClassDictionary node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitClassEntry(ClassEntry node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitClassInterface(ClassInterface node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitClassName(ClassName node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitClazz(Clazz node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitClientEntityList(ClientEntityList node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitClientRelation(ClientRelation node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitCluster(Cluster node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitClusterChart(ClusterChart node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitClusterEntry(ClusterEntry node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitContractClause(ContractClause node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitCreationChart(CreationChart node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitCreationEntry(CreationEntry node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitDictionaryEntry(DictionaryEntry node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitDynamicDiagram(DynamicDiagram node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitEventChart(EventChart node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitEventEntry(EventEntry node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitFeature(Feature node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitFeatureArgument(FeatureArgument node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitFeatureSpecification(FeatureSpecification node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitFormalGeneric(FormalGeneric node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitGenericIndirection(GenericIndirection node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitHasType(HasType node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitIndexClause(IndexClause node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitIndexing(Indexing node) {
    for (IndexClause clause : node.getIndexes()) {
      clause.accept(this);
      tp.printLine();
    }
  }

  @Override
  public void visitIndirectionFeatureList(IndirectionFeatureList node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitInheritanceRelation(InheritanceRelation node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitIntegerConstant(IntegerConstant node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitIntegerInterval(IntegerInterval node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitKeywordConstant(KeywordConstant node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitLabelledAction(LabelledAction node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitMemberRange(MemberRange node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitMultiplicity(Multiplicity node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitNamedIndirection(NamedIndirection node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitObjectGroup(ObjectGroup node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitObjectInstance(ObjectInstance node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitObjectName(ObjectName node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitObjectStack(ObjectStack node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitParentIndirection(ParentIndirection node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitQuantification(Quantification node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitRealConstant(RealConstant node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitRenameClause(RenameClause node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitScenarioChart(ScenarioChart node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitScenarioDescription(ScenarioDescription node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitScenarioEntry(ScenarioEntry node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitSetConstant(SetConstant node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitStaticDiagram(StaticDiagram node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitStringConstant(StringConstant node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitSupplierIndirection(SupplierIndirection node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitSystemChart(SystemChart node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitType(Type node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitTypeMark(TypeMark node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitTypeRange(TypeRange node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitUnaryExp(UnaryExp node) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void visitUnqualifiedCall(UnqualifiedCall node) {
    // TODO Auto-generated method stub
    
  }

  
  
}
