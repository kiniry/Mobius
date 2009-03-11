/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.printer;

public class PrintingTracker {

  private int numberOfEventCharts;
  private int numberOfScenarioCharts;
  private int numberOfCreationCharts;
  private int numberOfClassDictionaries;
  
  public PrintingTracker() {
    this.numberOfEventCharts = 0;
    this.numberOfScenarioCharts = 0;
    this.numberOfCreationCharts = 0;
    this.numberOfClassDictionaries = 0;
  }
  
  public String addEventChart() {
    return "" + (++numberOfEventCharts);
  }

  public String addScenarioChart() {
    return "" + (++numberOfScenarioCharts);
  }
  
  public String addCreationChart() {
    return "" + (++numberOfCreationCharts);
  }

  public String addClassDictionary() {
    return "" + (++numberOfClassDictionaries);
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
}

