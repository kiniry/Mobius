package ie.ucd.bon.printer;

import ie.ucd.bon.parser.tracker.ParsingTracker;

import java.util.Set;

public class HTMLLinkGenerator {

  private static final String SYSTEM_CHART = "system_chart:";
  private static final String CLASS_CHART = "class_chart:";
  private static final String CLUSTER_CHART = "cluster_chart:";
  private static final String EVENT_CHART = "event_chart:";
  private static final String SCENARIO_CHART = "scenario_chart:";
  private static final String CREATION_CHART = "creation_chart:";
  
  public static String generateLinks(PrintingTracker printingTracker, ParsingTracker parsingTracker) {
    StringBuilder sb = new StringBuilder();
    sb.append(generateJSIDs(printingTracker, parsingTracker));
    sb.append('\n');
    sb.append(generateFormJS(printingTracker, parsingTracker));
    return sb.toString();
  }
  
  private static String generateFormJS(PrintingTracker printingTracker, ParsingTracker parsingTracker) {
    StringBuilder sb = new StringBuilder();
    
    sb.append("var topOptions = [ ");
    sb.append("'System Chart', 'system_chart',");
    sb.append("'Cluster Charts', 'cluster_chart',");
    sb.append("'Class Charts', 'class_chart',");
    sb.append("'Event Charts', 'event_chart',");
    sb.append("'Scenario Charts', 'scenario_chart',");
    sb.append("'Creation Charts', 'creation_chart'");
    sb.append(" ];");
    sb.append('\n');
    
    sb.append("var subOptions = [];");
    sb.append('\n');
    
    sb.append("subOptions['system_chart'] = [ '");
    String systemName = parsingTracker.getInformalTypingInformation().getSystem().getSystemName();
    sb.append(systemName);
    sb.append("', '");
    sb.append(SYSTEM_CHART + systemName);
    sb.append("' ];");
    sb.append('\n');
    
    sb.append("subOptions['cluster_chart'] = [ ");
    Set<String> clusterNames = parsingTracker.getInformalTypingInformation().getClusters().keySet();
    for (String clusterName : clusterNames) {
      sb.append("'" + clusterName + "',");
      sb.append("'" + CLUSTER_CHART + clusterName + "',");
    } 
    if (clusterNames.size() > 0) {
      sb.deleteCharAt(sb.length()-1);
    }
    sb.append(" ];");
    sb.append('\n');
    
    sb.append("subOptions['class_chart'] = [ ");
    Set<String> classNames = parsingTracker.getInformalTypingInformation().getClasses().keySet();
    for (String className : classNames) {
      sb.append("'" + className + "',");
      sb.append("'" + CLASS_CHART + className + "',");
    } 
    if (clusterNames.size() > 0) {
      sb.deleteCharAt(sb.length()-1);
    }
    sb.append(" ];");
    sb.append('\n');
    
    
    sb.append("subOptions['event_chart'] = [ ");
    for (int i=1; i <= printingTracker.getNumberOfEventCharts(); i++) {
      sb.append("'Event Chart " + i + "',");
      sb.append("'" + EVENT_CHART + i + "',");
    } 
    if (printingTracker.getNumberOfEventCharts() > 0) {
      sb.deleteCharAt(sb.length()-1);
    }
    sb.append(" ];");
    sb.append('\n');
    
    sb.append("subOptions['creation_chart'] = [ ");
    for (int i=1; i <= printingTracker.getNumberOfCreationCharts(); i++) {
      sb.append("'Creation Chart " + i + "',");
      sb.append("'" + CREATION_CHART + i + "',");
    } 
    if (printingTracker.getNumberOfCreationCharts() > 0) {
      sb.deleteCharAt(sb.length()-1);
    }
    sb.append(" ];");
    sb.append('\n');
    
    sb.append("subOptions['scenario_chart'] = [ ");
    for (int i=1; i <= printingTracker.getNumberOfScenarioCharts(); i++) {
      sb.append("'Scenario Chart " + i + "',");
      sb.append("'" + SCENARIO_CHART + i + "',");
    } 
    if (printingTracker.getNumberOfScenarioCharts() > 0) {
      sb.deleteCharAt(sb.length()-1);
    }
    sb.append(" ];");
    sb.append('\n');
    
    return sb.toString();
  }
  
  private static String generateJSIDs(PrintingTracker printingTracker, ParsingTracker parsingTracker) {
    
    StringBuilder sb = new StringBuilder();
    sb.append("var items = [");
    
    appendItem(sb, SYSTEM_CHART + parsingTracker.getInformalTypingInformation().getSystem().getSystemName());
    
    Set<String> classNames = parsingTracker.getInformalTypingInformation().getClasses().keySet();
    for (String className : classNames) {
      appendItem(sb, CLASS_CHART + className);
    }
    
    Set<String> clusterNames = parsingTracker.getInformalTypingInformation().getClusters().keySet();
    for (String clusterName : clusterNames) {
      appendItem(sb, CLUSTER_CHART + clusterName);
    }
    
    for (int i=1; i <= printingTracker.getNumberOfEventCharts(); i++) {
      appendItem(sb, EVENT_CHART + i);
    }
    for (int i=1; i <= printingTracker.getNumberOfCreationCharts(); i++) {
      appendItem(sb, CREATION_CHART + i);
    }
    for (int i=1; i <= printingTracker.getNumberOfScenarioCharts(); i++) {
      appendItem(sb, SCENARIO_CHART + i);
    }
    
    if (sb.length() == 0) {
      return "";
    } else {
      return sb.substring(0,sb.length()-1).concat("];");
    }
  } 
 
  private static void appendItem(StringBuilder sb, String item) {
    sb.append('\'');
    sb.append(item);
    sb.append('\'');
    sb.append(',');
  }
  
}
