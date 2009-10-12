package ie.ucd.bon.printer;

import ie.ucd.bon.ast.AbstractVisitorWithAdditions;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClassDictionary;
import ie.ucd.bon.ast.ClassEntry;
import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.ClusterEntry;
import ie.ucd.bon.ast.CreationChart;
import ie.ucd.bon.ast.CreationEntry;
import ie.ucd.bon.ast.DictionaryEntry;
import ie.ucd.bon.ast.EventChart;
import ie.ucd.bon.ast.EventEntry;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.ScenarioChart;
import ie.ucd.bon.ast.ScenarioEntry;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.printer.template.FreeMarkerTemplate;
import ie.ucd.bon.printer.template.IsClusterMethod;
import ie.ucd.bon.source.SourceLocation;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;
import java.util.Map;

public class XHTMLPrintVisitor extends AbstractVisitorWithAdditions implements PrintAgent {

  public static final String CLASS_CHART_TEMPLATE = "xhtml-classchart.ftl";
  public static final String CLUSTER_CHART_TEMPLATE = "xhtml-clusterchart.ftl";
  public static final String SYSTEM_CHART_TEMPLATE = "xhtml-systemchart.ftl";
  public static final String CREATION_CHART_TEMPLATE = "xhtml-creationchart.ftl";
  public static final String EVENT_CHART_TEMPLATE = "xhtml-eventchart.ftl";
  public static final String SCENARIO_CHART_TEMPLATE = "xhtml-scenariochart.ftl";
  public static final String CLASS_DICT_TEMPLATE = "xhtml-classdict.ftl";

  private final PrintWriter writer;
  private final ByteArrayOutputStream baos;
  private final ParsingTracker tracker;

  public XHTMLPrintVisitor(ParsingTracker tracker) {
    baos = new ByteArrayOutputStream();
    writer = new PrintWriter(baos);
    this.tracker = tracker;
  }

  public String getAllOutputAsString(ParsingTracker tracker, Map<String,Object> data) throws IOException {
    String links = HTMLLinkGenerator.generateLinks(tracker);
    data.put("links", links);

    ByteArrayOutputStream start = new ByteArrayOutputStream();
    FreeMarkerTemplate.writeTemplate(new PrintWriter(start), "xhtml-start.ftl", data);
    ByteArrayOutputStream end = new ByteArrayOutputStream();
    FreeMarkerTemplate.writeTemplate(new PrintWriter(end), "xhtml-end.ftl", data);

    StringBuilder sb = new StringBuilder();
    sb.append(start.toString());
    sb.append(baos.toString());
    sb.append(end.toString());
    return sb.toString();
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

  private int classDicId = 1;

  @Override
  public void visitClassDictionary(ClassDictionary node, String systemName,
      List<DictionaryEntry> entries, Indexing indexing, String explanation,
      String part, SourceLocation loc) {
    FreeMarkerTemplate template = new FreeMarkerTemplate();
    template.addToDataModel("systemName", systemName);
    template.addToDataModel("entries", entries);
    template.addToDataModel("indexing", indexing);
    template.addToDataModel("explanation", explanation);
    template.addToDataModel("part", part);
    template.addToDataModel("id", "" + classDicId++);
    template.writeTemplate(writer, CLASS_DICT_TEMPLATE);
  }

  @Override
  public void visitClusterChart(ClusterChart node, String name,
      Boolean isSystem, List<ClassEntry> classes, List<ClusterEntry> clusters,
      Indexing indexing, String explanation, String part, SourceLocation loc) {
    FreeMarkerTemplate template = new FreeMarkerTemplate();
    template.addToDataModel("name", name);
    template.addToDataModel("classes", classes);
    template.addToDataModel("clusters", clusters);
    template.addToDataModel("indexing", indexing);
    template.addToDataModel("explanation", explanation);
    template.addToDataModel("part", part);

    if (isSystem) {
      template.writeTemplate(writer, SYSTEM_CHART_TEMPLATE);
    } else {
      template.writeTemplate(writer, CLUSTER_CHART_TEMPLATE);
    }
  }

  private int creationChartId = 1;

  @Override
  public void visitCreationChart(CreationChart node, String name,
      List<CreationEntry> entries, Indexing indexing, String explanation,
      String part, SourceLocation loc) {
    FreeMarkerTemplate template = new FreeMarkerTemplate();
    template.addToDataModel("name", name);
    template.addToDataModel("entries", entries);
    template.addToDataModel("indexing", indexing);
    template.addToDataModel("explanation", explanation);
    template.addToDataModel("part", part);
    template.addToDataModel("id", creationChartId++ + "");
    template.writeTemplate(writer, CREATION_CHART_TEMPLATE);
  }

  private int eventChartId = 1;

  @Override
  public void visitEventChart(EventChart node, String systemName,
      Boolean incoming, Boolean outgoing, List<EventEntry> entries,
      Indexing indexing, String explanation, String part, SourceLocation loc) {
    FreeMarkerTemplate template = new FreeMarkerTemplate();
    template.addToDataModel("systemName", systemName);
    template.addToDataModel("incoming", incoming);
    template.addToDataModel("outgoing", outgoing);
    template.addToDataModel("entries", entries);
    template.addToDataModel("indexing", indexing);
    template.addToDataModel("explanation", explanation);
    template.addToDataModel("part", part);
    template.addToDataModel("id", eventChartId++ + "");
    template.addToDataModel("isCluster", new IsClusterMethod(tracker.getSymbolTable().informal));
    template.writeTemplate(writer, EVENT_CHART_TEMPLATE);
  }

  private int scenarioChartId = 1;

  @Override
  public void visitScenarioChart(ScenarioChart node, String systemName,
      List<ScenarioEntry> entries, Indexing indexing, String explanation,
      String part, SourceLocation loc) {
    FreeMarkerTemplate template = new FreeMarkerTemplate();
    template.addToDataModel("systemName", systemName);
    template.addToDataModel("entries", entries);
    template.addToDataModel("indexing", indexing);
    template.addToDataModel("explanation", explanation);
    template.addToDataModel("part", part);
    template.addToDataModel("id", scenarioChartId++ + "");
    template.writeTemplate(writer, SCENARIO_CHART_TEMPLATE);
  }

}
