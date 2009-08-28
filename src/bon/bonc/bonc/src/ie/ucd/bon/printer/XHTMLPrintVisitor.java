package ie.ucd.bon.printer;

import ie.ucd.bon.ast.AbstractVisitorWithAdditions;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClassEntry;
import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.ClusterEntry;
import ie.ucd.bon.ast.CreationChart;
import ie.ucd.bon.ast.CreationEntry;
import ie.ucd.bon.ast.EventChart;
import ie.ucd.bon.ast.EventEntry;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.ScenarioChart;
import ie.ucd.bon.ast.ScenarioEntry;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.printer.template.FreeMarkerTemplate;
import ie.ucd.bon.source.SourceLocation;

import java.io.OutputStream;
import java.io.PrintWriter;
import java.util.List;

public class XHTMLPrintVisitor extends AbstractVisitorWithAdditions {
  
  public static final String CLASS_CHART_TEMPLATE = "xhtml-classchart.ftl";

  private final PrintWriter writer;
  
  public XHTMLPrintVisitor(OutputStream ps) {
    writer = new PrintWriter(ps);
  }

  @Override
  public void visitBonSourceFile(BonSourceFile node, List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation loc) {
    visitAll(bonSpecification);
  }

  @Override
  public void visitClassChart(ClassChart node, ClassName name,
      List<ClassName> inherits, List<String> queries, List<String> commands,
      List<String> constraints, Indexing indexing, String explanation,
      String part, SourceLocation loc) {

    FreeMarkerTemplate template = new FreeMarkerTemplate();
    
    template.addToDataModel("name", name);
    template.addToDataModel("inherits", inherits);
    template.addToDataModel("queries", queries);
    template.addToDataModel("commands", commands);
    template.addToDataModel("constraints", constraints);
    template.addToDataModel("indexing", indexing);
    template.addToDataModel("explanation", explanation);
    template.addToDataModel("part", part);
    
    template.writeTemplate(writer, CLASS_CHART_TEMPLATE);
  }

  @Override
  public void visitClusterChart(ClusterChart node, String name,
      Boolean isSystem, List<ClassEntry> classes, List<ClusterEntry> clusters,
      Indexing indexing, String explanation, String part, SourceLocation loc) {
    // TODO Auto-generated method stub
    super.visitClusterChart(node, name, isSystem, classes, clusters, indexing,
        explanation, part, loc);
  }

  @Override
  public void visitCreationChart(CreationChart node, String name,
      List<CreationEntry> entries, Indexing indexing, String explanation,
      String part, SourceLocation loc) {
    // TODO Auto-generated method stub
    super.visitCreationChart(node, name, entries, indexing, explanation, part, loc);
  }

  @Override
  public void visitEventChart(EventChart node, String systemName,
      Boolean incoming, Boolean outgoing, List<EventEntry> entries,
      Indexing indexing, String explanation, String part, SourceLocation loc) {
    // TODO Auto-generated method stub
    super.visitEventChart(node, systemName, incoming, outgoing, entries, indexing,
        explanation, part, loc);
  }

  @Override
  public void visitScenarioChart(ScenarioChart node, String systemName,
      List<ScenarioEntry> entries, Indexing indexing, String explanation,
      String part, SourceLocation loc) {
    // TODO Auto-generated method stub
    super.visitScenarioChart(node, systemName, entries, indexing, explanation,
        part, loc);
  }
  
  
  
}
