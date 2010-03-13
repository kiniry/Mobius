
/**
 * Copyright (c) 2007-2010, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from normal_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

public class CreationChart extends InformalChart {


  public final Indexing indexing;

  public final String name;
  public final List<CreationEntry> entries;
  public final String explanation;
  public final String part;


  // === Constructors and Factories ===
  protected CreationChart(String name, List<CreationEntry> entries, Indexing indexing, String explanation, String part, SourceLocation location) {
    super(location);
    this.name = name; assert name != null;
    this.entries = entries; assert entries != null;
    this.indexing = indexing; 
    this.explanation = explanation; 
    this.part = part; 
  }

  public static CreationChart mk(String name, List<CreationEntry> entries, Indexing indexing, String explanation, String part, SourceLocation location) {
    return new CreationChart(name, entries, indexing, explanation, part, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public List<CreationEntry> getEntries() { return entries; }
  public Indexing getIndexing() { return indexing; }
  public String getExplanation() { return explanation; }
  public String getPart() { return part; }

  // === Visitor ===
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitCreationChart(this, name, entries, indexing, explanation, part, getLocation());
  }

  // === Others ===
  @Override
  public CreationChart clone() {
    String newName = name;
    List<CreationEntry> newEntries = entries;
    Indexing newIndexing = indexing == null ? null : indexing.clone();
    String newExplanation = explanation;
    String newPart = part;
    return CreationChart.mk(newName, newEntries, newIndexing, newExplanation, newPart, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

