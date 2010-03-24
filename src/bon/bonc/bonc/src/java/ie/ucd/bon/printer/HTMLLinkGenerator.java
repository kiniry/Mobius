/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.printer;

import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.BONST;

import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

public class HTMLLinkGenerator {

  private static final String SYSTEM_CHART = "system_chart:";
  private static final String CLASS_CHART = "class_chart:";
  private static final String CLUSTER_CHART = "cluster_chart:";
  private static final String EVENT_CHART = "event_chart:";
  private static final String SCENARIO_CHART = "scenario_chart:";
  private static final String CREATION_CHART = "creation_chart:";
  private static final String CLASS_DICTIONARY = "class_dictionary:";

  public static String generateLinks(ParsingTracker parsingTracker) {
    BONST.BONSTInformal st = parsingTracker.getSymbolTable().informal;
    PrintingCountVisitor counter = new PrintingCountVisitor();
    for (ParseResult parse : parsingTracker.getParses()) {
      if (parse.getParse() != null) {
        parse.getParse().accept(counter);
      }
    }

    StringBuilder sb = new StringBuilder();
    sb.append(generateJSIDs(st, counter));
    sb.append('\n');
    sb.append(generateFormJS(st, counter));
    return sb.toString();
  }

  private static String generateFormJS(BONST.BONSTInformal st, PrintingCountVisitor counter) {
    StringBuilder sb = new StringBuilder();

    sb.append("var topOptions = [ ");

    if (st.systemChart != null) {
      sb.append("'System Chart', 'system_chart', ");
    }

    if (counter.getNumberOfClassDictionaries() > 0) {
      sb.append("'Class Dictionaries', 'class_dictionary', ");
    }
    if (!st.clusters.isEmpty()) {
      sb.append("'Cluster Charts', 'cluster_chart', ");
    }
    if (!st.classes.isEmpty()) {
      sb.append("'Class Charts', 'class_chart', ");
    }
    if (counter.getNumberOfEventCharts() > 0) {
      sb.append("'Event Charts', 'event_chart', ");
    }
    if (counter.getNumberOfScenarioCharts() > 0) {
      sb.append("'Scenario Charts', 'scenario_chart', ");
    }
    if (counter.getNumberOfCreationCharts() > 0) {
      sb.append("'Creation Charts', 'creation_chart', ");
    }

    sb.deleteCharAt(sb.length()-1);
    sb.deleteCharAt(sb.length()-1);

    sb.append(" ];");
    sb.append('\n');

    sb.append("var subOptions = [];");
    sb.append('\n');

    if (st.systemChart != null) {
      sb.append("subOptions['system_chart'] = [ '");
      String systemName = st.systemChart.name;
      sb.append(systemName);
      sb.append("', '");
      sb.append(SYSTEM_CHART + systemName);
      sb.append("' ];");
      sb.append('\n');
    }

    if (!st.clusters.isEmpty()) {
      sb.append("subOptions['cluster_chart'] = [ ");
      SortedSet<String> clusterNames = new TreeSet<String>(st.clusters.keySet());
      for (String clusterName : clusterNames) {
        sb.append("'" + clusterName + "',");
        sb.append("'" + CLUSTER_CHART + clusterName + "',");
      }
      if (clusterNames.size() > 0) {
        sb.deleteCharAt(sb.length()-1);
      }
      sb.append(" ];");
      sb.append('\n');
    }

    if (!st.classes.isEmpty()) {
      sb.append("subOptions['class_chart'] = [ ");
      SortedSet<String> classNames = new TreeSet<String>(st.classes.keySet());
      for (String className : classNames) {
        sb.append("'" + className + "',");
        sb.append("'" + CLASS_CHART + className + "',");
      }
      if (classNames.size() > 0) {
        sb.deleteCharAt(sb.length()-1);
      }
      sb.append(" ];");
      sb.append('\n');
    }

    if (counter.getNumberOfEventCharts() > 0) {
      sb.append("subOptions['event_chart'] = [ ");
      for (int i=1; i <= counter.getNumberOfEventCharts(); i++) {
        sb.append("'Event Chart " + i + "',");
        sb.append("'" + EVENT_CHART + i + "',");
      }
      if (counter.getNumberOfEventCharts() > 0) {
        sb.deleteCharAt(sb.length()-1);
      }
      sb.append(" ];");
      sb.append('\n');
    }

    if (counter.getNumberOfCreationCharts() > 0) {
      sb.append("subOptions['creation_chart'] = [ ");
      for (int i=1; i <= counter.getNumberOfCreationCharts(); i++) {
        sb.append("'Creation Chart " + i + "',");
        sb.append("'" + CREATION_CHART + i + "',");
      }
      if (counter.getNumberOfCreationCharts() > 0) {
        sb.deleteCharAt(sb.length()-1);
      }
      sb.append(" ];");
      sb.append('\n');
    }

    if (counter.getNumberOfScenarioCharts() > 0) {
      sb.append("subOptions['scenario_chart'] = [ ");
      for (int i=1; i <= counter.getNumberOfScenarioCharts(); i++) {
        sb.append("'Scenario Chart " + i + "',");
        sb.append("'" + SCENARIO_CHART + i + "',");
      }
      if (counter.getNumberOfScenarioCharts() > 0) {
        sb.deleteCharAt(sb.length()-1);
      }
      sb.append(" ];");
      sb.append('\n');
    }

    if (counter.getNumberOfClassDictionaries() > 0) {
      sb.append("subOptions['class_dictionary'] = [ ");
      for (int i=1; i <= counter.getNumberOfClassDictionaries(); i++) {
        sb.append("'Class Dictionary " + i + "',");
        sb.append("'" + CLASS_DICTIONARY + i + "',");
      }
      if (counter.getNumberOfClassDictionaries() > 0) {
        sb.deleteCharAt(sb.length()-1);
      }
      sb.append(" ];");
      sb.append('\n');
    }

    return sb.toString();
  }

  private static String generateJSIDs(BONST.BONSTInformal st, PrintingCountVisitor counter) {
    StringBuilder sb = new StringBuilder();
    sb.append("var items = [");

    if (st.systemChart != null) {
      appendItem(sb, SYSTEM_CHART + st.systemChart.getName());
    }

    Set<String> classNames = st.classes.keySet();
    for (String className : classNames) {
      appendItem(sb, CLASS_CHART + className);
    }

    Set<String> clusterNames = st.clusters.keySet();
    for (String clusterName : clusterNames) {
      appendItem(sb, CLUSTER_CHART + clusterName);
    }

    for (int i=1; i <= counter.getNumberOfEventCharts(); i++) {
      appendItem(sb, EVENT_CHART + i);
    }
    for (int i=1; i <= counter.getNumberOfCreationCharts(); i++) {
      appendItem(sb, CREATION_CHART + i);
    }
    for (int i=1; i <= counter.getNumberOfScenarioCharts(); i++) {
      appendItem(sb, SCENARIO_CHART + i);
    }
    for (int i=1; i <= counter.getNumberOfClassDictionaries(); i++) {
      appendItem(sb, CLASS_DICTIONARY + i);
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
