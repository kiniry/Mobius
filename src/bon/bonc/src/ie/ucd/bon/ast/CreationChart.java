
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.ast.AstNode;

public class CreationChart extends InformalChart {


  private final Indexing indexing;

  private final String name;
  private final List<CreationEntry> entries;
  private final String explanation;
  private final String part;

  private final SourceLocation location;

  // === Constructors and Factories ===
  protected CreationChart(String name, List<CreationEntry> entries, Indexing indexing, String explanation, String part) {
    this(name,entries,indexing,explanation,part, null);    
  }

  protected CreationChart(String name, List<CreationEntry> entries, Indexing indexing, String explanation, String part, SourceLocation location) {
    
    assert location != null;
    this.location = location;
    this.name = name; assert name != null;
    this.entries = entries; assert entries != null;
    this.indexing = indexing; 
    this.explanation = explanation; 
    this.part = part; 
    
  }
  
  public static CreationChart mk(String name, List<CreationEntry> entries, Indexing indexing, String explanation, String part) {
    return new CreationChart(name, entries, indexing, explanation, part);
  }

  public static CreationChart mk(String name, List<CreationEntry> entries, Indexing indexing, String explanation, String part, SourceLocation location) {
    return new CreationChart(name, entries, indexing, explanation, part, location);
  }
  
  public SourceLocation getLocation() {
    return location;
  }

  // === Accessors ===

  public String getName() { return name; }
  public List<CreationEntry> getEntries() { return entries; }
  public Indexing getIndexing() { return indexing; }
  public String getExplanation() { return explanation; }
  public String getPart() { return part; }

  // === Others ===
  @Override
  public CreationChart clone() {
    String newName = name;
    List<CreationEntry> newEntries = entries;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    String newExplanation = explanation;
    String newPart = part;
    
    return CreationChart.mk(newName, newEntries, newIndexing, newExplanation, newPart, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("CreationChart ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("entries = ");
    sb.append(entries);
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

