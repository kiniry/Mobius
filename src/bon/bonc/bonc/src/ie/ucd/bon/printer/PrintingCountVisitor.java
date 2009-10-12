/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.printer;

import java.util.List;

import ie.ucd.bon.ast.AbstractVisitorWithAdditions;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClassDictionary;
import ie.ucd.bon.ast.CreationChart;
import ie.ucd.bon.ast.CreationEntry;
import ie.ucd.bon.ast.DictionaryEntry;
import ie.ucd.bon.ast.EventChart;
import ie.ucd.bon.ast.EventEntry;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.ScenarioChart;
import ie.ucd.bon.ast.ScenarioEntry;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.source.SourceLocation;

public class PrintingCountVisitor extends AbstractVisitorWithAdditions {

  private int numberOfEventCharts;
  private int numberOfScenarioCharts;
  private int numberOfCreationCharts;
  private int numberOfClassDictionaries;
  
  public PrintingCountVisitor() {
    this.numberOfEventCharts = 0;
    this.numberOfScenarioCharts = 0;
    this.numberOfCreationCharts = 0;
    this.numberOfClassDictionaries = 0;
  }
  
  @Override
  public void visitBonSourceFile(BonSourceFile node, List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation loc) {
    visitAll(bonSpecification);
  }

  @Override
  public void visitClassDictionary(ClassDictionary node, String systemName, List<DictionaryEntry> entries, Indexing indexing, String explanation, String part, SourceLocation loc) {
    numberOfClassDictionaries++;
  }

  @Override
  public void visitCreationChart(CreationChart node, String name, List<CreationEntry> entries, Indexing indexing, String explanation, String part, SourceLocation loc) {
    numberOfCreationCharts++;
  }

  @Override
  public void visitEventChart(EventChart node, String systemName, Boolean incoming, Boolean outgoing, List<EventEntry> entries, Indexing indexing, String explanation, String part, SourceLocation loc) {
    numberOfEventCharts++;
  }

  @Override
  public void visitScenarioChart(ScenarioChart node, String systemName, List<ScenarioEntry> entries, Indexing indexing, String explanation, String part, SourceLocation loc) {
    numberOfScenarioCharts++;
  }
  
  public int getNumberOfEventCharts() {
    return numberOfEventCharts;
  }
  
  public int getNumberOfScenarioCharts() {
    return numberOfScenarioCharts;
  }
  
  public int getNumberOfCreationCharts() {
    return numberOfCreationCharts;
  }

  public int getNumberOfClassDictionaries() {
    return numberOfClassDictionaries;
  }
  
  public String toString() {
    return "Counted " + numberOfClassDictionaries + " class dictionaries, " + numberOfCreationCharts + " creation charts, " + numberOfEventCharts + " event charts, " + numberOfScenarioCharts + " scenario charts";
  }
}

