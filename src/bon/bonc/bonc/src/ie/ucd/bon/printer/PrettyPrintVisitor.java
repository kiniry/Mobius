package ie.ucd.bon.printer;

import ie.ucd.bon.ast.AbstractVisitor;
import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BinaryExp;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.BooleanConstant;
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
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.ClusterEntry;
import ie.ucd.bon.ast.DictionaryEntry;
import ie.ucd.bon.ast.EnumerationElement;
import ie.ucd.bon.ast.Expression;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.GenericIndirection;
import ie.ucd.bon.ast.HasType;
import ie.ucd.bon.ast.IVisitor;
import ie.ucd.bon.ast.IndexClause;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.IndirectionElement;
import ie.ucd.bon.ast.IndirectionFeaturePart;
import ie.ucd.bon.ast.InheritanceRelation;
import ie.ucd.bon.ast.IntegerConstant;
import ie.ucd.bon.ast.IntegerInterval;
import ie.ucd.bon.ast.KeywordConstant;
import ie.ucd.bon.ast.LabelledAction;
import ie.ucd.bon.ast.MemberRange;
import ie.ucd.bon.ast.Multiplicity;
import ie.ucd.bon.ast.NamedIndirection;
import ie.ucd.bon.ast.Quantification;
import ie.ucd.bon.ast.RealConstant;
import ie.ucd.bon.ast.SetConstant;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.ast.StaticRef;
import ie.ucd.bon.ast.StringConstant;
import ie.ucd.bon.ast.SupplierIndirection;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.ast.TypeMark;
import ie.ucd.bon.ast.TypeRange;
import ie.ucd.bon.ast.UnaryExp;
import ie.ucd.bon.ast.VariableRange;
import ie.ucd.bon.ast.BinaryExp.Op;
import ie.ucd.bon.ast.Clazz.Mod;
import ie.ucd.bon.ast.KeywordConstant.Constant;
import ie.ucd.bon.ast.Quantification.Quantifier;
import ie.ucd.bon.ast.TypeMark.Mark;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

import java.io.PrintStream;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

public class PrettyPrintVisitor extends AbstractVisitor implements IVisitor {

  private final TextPrinter tp;

  public PrettyPrintVisitor(PrintStream ps) {
    tp = new TextPrinter(ps);
  }

  @Override
  public void visitBonSourceFile(BonSourceFile node,
      List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation loc) {
    if (indexing != null) {
      indexing.accept(this);
      tp.printLine();
    }
    for (SpecificationElement spec : bonSpecification) {
      spec.accept(this);
    }
  }

  @Override
  public void visitBooleanConstant(BooleanConstant node, Boolean value, SourceLocation loc) {
    tp.print(value.toString());
  }

  @Override
  public void visitClassName(ClassName node, String name, SourceLocation loc) {
    tp.print(name);
  }

  @Override
  public void visitClazz(Clazz node, ClassName name, List<FormalGeneric> generics,
      Mod mod, ClassInterface classInterface, Boolean reused,
      Boolean persistent, Boolean interfaced, String comment, SourceLocation loc) {
    tp.print(toString(mod));
    tp.print(name.getName());

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
  public void visitBinaryExp(BinaryExp node, Op op, Expression left,
      Expression right, SourceLocation loc) {
    left.accept(this);
    tp.printSpace();
    printBinaryExpOp(op);
    tp.printSpace();
    right.accept(this);
  }

  @Override
  public void visitUnaryExp(UnaryExp node, ie.ucd.bon.ast.UnaryExp.Op op,
      Expression expression, SourceLocation loc) {
    printUnaryExpOp(op);
    tp.printSpace();
    expression.accept(this);
  }

  @Override
  public void visitIndexClause(IndexClause node, String id, List<String> indexTerms, SourceLocation loc) {
    tp.startLine();
    tp.print(id);
    tp.print(':');
    tp.print(StringUtil.appendWithSeparator(indexTerms, ", "));
    tp.printLine(";");
  }

  @Override
  public void visitIndexing(Indexing node, List<IndexClause> indexes, SourceLocation loc) {
    tp.startLine();
    tp.printLine("indexing");
    tp.increaseIndentation();
    visitAll(indexes);
    tp.decreaseIndentation();
  }

  @Override
  public void visitSetConstant(SetConstant node, List<EnumerationElement> enumerations, SourceLocation loc) {
    tp.print('{');
    visitAllPrintingSeparator(enumerations, ", ", false);
    tp.print('}');
    super.visitSetConstant(node, enumerations, loc);
  }

  @Override
  public void visitQuantification(Quantification node, Quantifier quantifier,
      List<VariableRange> variableRanges, Expression restriction,
      Expression proposition, SourceLocation loc) {
    printQuantifier(quantifier);
    tp.printSpace();
    visitAllPrintingSeparator(variableRanges, "; ", true);
    visitNodeIfNonNull(restriction);
    proposition.accept(this);
  }

  @Override
  public void visitClassChart(ClassChart node, ClassName name,
      List<ClassName> inherits, List<String> queries, List<String> commands,
      List<String> constraints, Indexing indexing, String explanation,
      String part, SourceLocation loc) {
    tp.print("class_chart ");
    name.accept(this);
    tp.printLine();
    tp.increaseIndentation();
    visitNodeIfNonNull(indexing);
    printExplanation(explanation);
    printPart(part);
    if (!queries.isEmpty()) {
      tp.printLine("query");
      tp.increaseIndentation();
      for (String query : queries) {
        tp.startLine();
        tp.printLine(query);
      }
      tp.decreaseIndentation();
    }
    if (!commands.isEmpty()) {
      tp.printLine("command");
      tp.increaseIndentation();
      for (String command : commands) {
        tp.startLine();
        tp.printLine(command);
      }
      tp.decreaseIndentation();
    }
    if (!constraints.isEmpty()) {
      tp.printLine("constraint");
      tp.increaseIndentation();
      for (String constraint : constraints) {
        tp.startLine();
        tp.printLine(constraint);
      }
      tp.decreaseIndentation();
    }
    tp.decreaseIndentation();
    tp.startLine();
    tp.printLine("end");
  }

  @Override
  public void visitClusterChart(ClusterChart node, String name,
      Boolean isSystem, List<ClassEntry> classes, List<ClusterEntry> clusters,
      Indexing indexing, String explanation, String part, SourceLocation loc) {
    tp.startLine();
    if (isSystem) {
      tp.printLine("system_chart ");
    } else {
      tp.printLine("cluster_chart ");
    }
    tp.printLine(name);
    tp.increaseIndentation();
    visitNodeIfNonNull(indexing);
    printExplanation(explanation);
    printPart(part);

    visitAll(classes);
    visitAll(clusters);
    tp.decreaseIndentation();
    tp.startLine();
    tp.printLine("end");
  }

  @Override
  public void visitClassDictionary(ClassDictionary node, String systemName,
      List<DictionaryEntry> entries, Indexing indexing, String explanation,
      String part, SourceLocation loc) {
    tp.startLine();
    tp.print("dictionary ");
    tp.printLine(systemName);
    tp.increaseIndentation();

    visitNodeIfNonNull(indexing);
    printExplanation(explanation);
    printPart(part);

    visitAll(entries);

    tp.decreaseIndentation();
    tp.startLine();
    tp.printLine("end");
  }

  @Override
  public void visitDictionaryEntry(DictionaryEntry node, String name,
      List<String> clusters, String description, SourceLocation loc) {
    tp.startLine();
    tp.print("class ");
    tp.print(name);
    tp.print(" cluster ");
    tp.print(StringUtil.appendWithSeparator(clusters, ", "));
    printDescription(description);
    tp.printLine();
  }

  @Override
  public void visitClassEntry(ClassEntry node, String name, String description, SourceLocation loc) {
    tp.startLine();
    tp.print("class ");
    tp.print(name);
    tp.print(description);
    tp.printLine();
  }

  @Override
  public void visitClusterEntry(ClusterEntry node, String name, String description, SourceLocation loc) {
    tp.startLine();
    tp.print("cluster ");
    tp.print(name);
    tp.print(description);
    tp.printLine();
  }

  @Override
  public void visitClientEntityList(ClientEntityList node, List<ClientEntity> entities, SourceLocation loc) {
    visitAllPrintingSeparator(entities, ", ", false);
  }

  @Override
  public void visitIntegerConstant(IntegerConstant node, Integer value, SourceLocation loc) {
    tp.print(value);
  }

  @Override
  public void visitIntegerInterval(IntegerInterval node, Integer start, Integer stop, SourceLocation loc) {
    tp.print(start);
    tp.print("..");
    tp.print(stop);
  }

  @Override
  public void visitKeywordConstant(KeywordConstant node, Constant constant, SourceLocation loc) {
    switch(constant) {
    case CURRENT:
      tp.print("Current");
      break;
    case RESULT:
      tp.print("Result");
      break;
    case VOID:
      tp.print("Void");
      break;
    }
  }

  @Override
  public void visitMultiplicity(Multiplicity node, Integer multiplicity, SourceLocation loc) {
    tp.print('{');
    tp.print(multiplicity);
    tp.print("} ");
  }

  @Override
  public void visitType(Type node, String identifier, List<Type> actualGenerics, String fullString, SourceLocation loc) {
    tp.print(identifier);
    if (!actualGenerics.isEmpty()) {
      tp.print('[');
      visitAllPrintingSeparator(actualGenerics, ", ", false);
      tp.print(']');
    }
  }

  @Override
  public void visitTypeMark(TypeMark node, Mark mark, Integer multiplicity, SourceLocation loc) {
    switch(mark) {
    case AGGREGATE:
      tp.print(":{");
      break;
    case HASTYPE:
      tp.print(':');
      break;
    case NONE:
      break;
    case SHAREDMARK:
      tp.print(":(");
      tp.print(multiplicity);
      tp.print(')');
      break;
    }
  }  

  @Override
  public void visitTypeRange(TypeRange node, List<String> identifiers, Type type, SourceLocation loc) {
    tp.print(StringUtil.appendWithSeparator(identifiers, ", "));
    tp.print(':');
    type.accept(this);
  }

  @Override
  public void visitClientRelation(ClientRelation node, StaticRef client,
      StaticRef supplier, ClientEntityExpression clientEntities,
      TypeMark typeMark, String semanticLabel, SourceLocation loc) {
    client.accept(this);
    tp.print(" client ");
    visitNodeIfNonNull(clientEntities);
    typeMark.accept(this);
    supplier.accept(this);
    printSemanticLabel(semanticLabel);
    tp.printLine();
  }

  @Override
  public void visitInheritanceRelation(InheritanceRelation node,
      StaticRef child, StaticRef parent, Multiplicity multiplicity,
      String semanticLabel, SourceLocation loc) {
    child.accept(this);
    tp.print(" inherit ");
    visitNodeIfNonNull(multiplicity);
    parent.accept(this);
    printSemanticLabel(semanticLabel);
    tp.printLine();
  }

  @Override
  public void visitSupplierIndirection(SupplierIndirection node,
      IndirectionFeaturePart indirectionFeaturePart,
      GenericIndirection genericIndirection, SourceLocation loc) {
    if (indirectionFeaturePart != null) {
      indirectionFeaturePart.accept(this);
      tp.print(" : ");
    }
    genericIndirection.accept(this);
  }
  
  @Override
  public void visitLabelledAction(LabelledAction node, String label,
      String description, SourceLocation loc) {
    tp.print(label);
    tp.printSpace();
    tp.print(description);
  }

  @Override
  public void visitMemberRange(MemberRange node, List<String> identifiers,
      Expression expression, SourceLocation loc) {
    tp.print(StringUtil.appendWithSeparator(identifiers, ", "));
    tp.print(" member_of ");
    expression.accept(this);
  }

  @Override
  public void visitRealConstant(RealConstant node, Double value, SourceLocation loc) {
    tp.print(value);
  }

  @Override
  public void visitStringConstant(StringConstant node, String value, SourceLocation loc) {
    tp.print(value);
  }

  @Override
  public void visitHasType(HasType node, TypeMark mark, Type type, SourceLocation loc) {
    mark.accept(this);
    tp.print(' ');
    type.accept(this);
  }

  @Override
  public void visitCharacterConstant(CharacterConstant node, Character value,
      SourceLocation loc) {
    tp.print('\'');
    tp.print(value);
    tp.print('\'');
  } 

  @Override
  public void visitCharacterInterval(CharacterInterval node, Character start,
      Character stop, SourceLocation loc) {
    tp.print('\'');
    tp.print(start);
    tp.print('\'');
    tp.print("..");
    tp.print('\'');
    tp.print(stop);
    tp.print('\'');
  }


  // **** END VISIT METHODS ****/

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

  protected void printUnaryExpOp(ie.ucd.bon.ast.UnaryExp.Op op) {
    switch (op) {
    case ADD:
      tp.print('+');
      break;
    case DELTA:
      tp.print("delta");
      break;
    case NOT:
      tp.print("not");
      break;
    case OLD:
      tp.print("old");
      break;
    case SUB:
      tp.print('-');
      break;
    }
  }

  protected void printBinaryExpOp(Op op) {
    switch (op) {
    case ADD:
      tp.print('+');
      break;
    case AND:
      tp.print("and");
      break;
    case DIV:
      tp.print('/');
      break;
    case EQ:
      tp.print('=');
      break;
    case EQUIV:
      tp.print("<->");
      break;
    case GE:
      tp.print(">=");
      break;
    case GT:
      tp.print('>');
      break;
    case HASTYPE:
      tp.print(':');
      break;
    case IMPLIES:
      tp.print("->");
      break;
    case INTDIV:
      tp.print("//");
      break;
    case LE:
      tp.print("<=");
      break;
    case LT:
      tp.print('<');
      break;
    case MEMBEROF:
      tp.print("member_of");
      break;
    case MOD:
      tp.print("\\\\");
      break;
    case MUL:
      tp.print('*');
      break;
    case NEQ:
      tp.print("/=");
      break;
    case NOTMEMBEROF:
      tp.print("not member_of");
      break;
    case OR:
      tp.print("or");
      break;
    case POW:
      tp.print('^');
      break;
    case SUB:
      tp.print('-');
      break;
    case XOR:
      tp.print("xor");
      break;
    }
  }

  protected void printQuantifier(Quantifier quantifier) {
    switch (quantifier) {
    case EXISTS:
      tp.print("exists");
      break;
    case FORALL:
      tp.print("for_all");
      break;
    }
  }

  protected final void visitNodeIfNonNull(AstNode node) {
    if (node != null) {
      node.accept(this);
    }
  }

  public void visitAllPrintingSeparator(Collection<? extends AstNode> nodes, String separator, boolean separatorAtEnd) {
    for (Iterator<? extends AstNode> it = nodes.iterator(); it.hasNext(); ) {
      it.next().accept(this);
      if (it.hasNext() || separatorAtEnd) {
        tp.print(separator);
      }
    }
  }

  protected void printExplanation(String explanation) {
    if (explanation != null) {
      tp.startLine();
      tp.printLine("explanation");
      tp.increaseIndentation();
      tp.startLine();
      tp.printLine(explanation);
      tp.decreaseIndentation();
    }
  }

  protected void printPart(String part) {
    if (part != null) {
      tp.startLine();
      tp.printLine("part");
      tp.increaseIndentation();
      tp.startLine();
      tp.printLine(part);
      tp.decreaseIndentation();
    }
  }

  protected void printDescription(String description) {
    tp.print(" description ");
    tp.print(description);
  }
  
  protected void printSemanticLabel(String label) {
    if (label != null) {
      tp.printSpace();
      tp.print(label);
    }
  }
}
