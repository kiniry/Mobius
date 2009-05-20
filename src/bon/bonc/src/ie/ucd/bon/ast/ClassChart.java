
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class ClassChart extends InformalChart {


  private final Indexing indexing;

  private final String name;
  private final List<String> inherits;
  private final List<String> queries;
  private final List<String> commands;
  private final List<String> constraints;
  private final String explanation;
  private final String part;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected ClassChart(String name, List<String> inherits, List<String> queries, List<String> commands, List<String> constraints, Indexing indexing, String explanation, String part) {
    this(name,inherits,queries,commands,constraints,indexing,explanation,part, null);    
  }

  protected ClassChart(String name, List<String> inherits, List<String> queries, List<String> commands, List<String> constraints, Indexing indexing, String explanation, String part, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.name = name; assert name != null;
    this.inherits = inherits; assert inherits != null;
    this.queries = queries; assert queries != null;
    this.commands = commands; assert commands != null;
    this.constraints = constraints; assert constraints != null;
    this.indexing = indexing; 
    this.explanation = explanation; 
    this.part = part; 
    
  }
  
  public static ClassChart mk(String name, List<String> inherits, List<String> queries, List<String> commands, List<String> constraints, Indexing indexing, String explanation, String part) {
    return new ClassChart(name, inherits, queries, commands, constraints, indexing, explanation, part);
  }

  public static ClassChart mk(String name, List<String> inherits, List<String> queries, List<String> commands, List<String> constraints, Indexing indexing, String explanation, String part, SourceLocation location) {
    return new ClassChart(name, inherits, queries, commands, constraints, indexing, explanation, part, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public String getName() { return name; }
  public List<String> getInherits() { return inherits; }
  public List<String> getQueries() { return queries; }
  public List<String> getCommands() { return commands; }
  public List<String> getConstraints() { return constraints; }
  public Indexing getIndexing() { return indexing; }
  public String getExplanation() { return explanation; }
  public String getPart() { return part; }

  // === Others ===
  @Override
  public ClassChart clone() {
    String newName = name;
    List<String> newInherits = inherits;
    List<String> newQueries = queries;
    List<String> newCommands = commands;
    List<String> newConstraints = constraints;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    String newExplanation = explanation;
    String newPart = part;
    
    return ClassChart.mk(newName, newInherits, newQueries, newCommands, newConstraints, newIndexing, newExplanation, newPart, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ClassChart ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("inherits = ");
    sb.append(inherits);
    sb.append(", ");
    
    sb.append("queries = ");
    sb.append(queries);
    sb.append(", ");
    
    sb.append("commands = ");
    sb.append(commands);
    sb.append(", ");
    
    sb.append("constraints = ");
    sb.append(constraints);
    sb.append(", ");
    
    sb.append("indexing = ");
    sb.append(indexing);
    sb.append(", ");
    
    sb.append("explanation = ");
    sb.append(explanation);
    sb.append(", ");
    
    sb.append("part = ");
    sb.append(part);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

