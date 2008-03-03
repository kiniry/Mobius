package ie.ucd.bon.printer;

public class PrintingTracker {

  private int numberOfEventCharts;
  private int numberOfScenarioCharts;
  private int numberOfCreationCharts;
  
  public PrintingTracker() {
    this.numberOfEventCharts = 0;
    this.numberOfScenarioCharts = 0;
    this.numberOfCreationCharts = 0;
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
  
  public int getNumberOfEventCharts() {
    return numberOfEventCharts;
  }
  
  public int getNumberOfScenarioCharts() {
    return numberOfScenarioCharts;
  }
  
  public int getNumberOfCreationCharts() {
    return numberOfCreationCharts;
  }
}

