/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.printer;

import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.informal.ClassChartDefinition;
import ie.ucd.bon.typechecker.informal.ClusterChartDefinition;
import ie.ucd.bon.typechecker.informal.InformalTypingInformation;
import ie.ucd.bon.typechecker.informal.SystemChartDefinition;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class ClassDictionaryGenerator {

  public static String generateDictionary(ParsingTracker tracker) throws UnableToGenerateClassDictionaryException {
    String newLine = System.getProperty("line.separator");
    
    StringBuilder sb = new StringBuilder();
    
    InformalTypingInformation iti = tracker.getInformalTypingInformation();
    SystemChartDefinition sysDef = iti.getSystem();
    Map<String,ClassChartDefinition> classes = iti.getClasses(); 
    Set<String> classNames = new TreeSet<String>(classes.keySet());
    Graph<String,ClusterChartDefinition> classClusterGraph = iti.getClassClusterGraph();
    
    
    
    if (sysDef == null) {
      throw new UnableToGenerateClassDictionaryException("No system defined!");
    }
    if (classNames.size() == 0) {
      throw new UnableToGenerateClassDictionaryException("No classes in system!");
    }

    sb.append("dictionary ");
    sb.append(sysDef.getSystemName());
    sb.append(newLine);
    
    sb.append("  explanation");
    sb.append(newLine);
    sb.append("    \"BONc automatically generated class dictionary.\"");
    sb.append(newLine);

    for (String className : classNames) {
      ClassChartDefinition classDef = classes.get(className);
      
      Set<ClusterChartDefinition> inClusters = classClusterGraph.getLinkedNodes(className);
      if (inClusters == null || inClusters.size() == 0) {
        //TODO or just ignore?
        throw new UnableToGenerateClassDictionaryException("Class " + className + " is not in any cluster!");
      } else {
        sb.append("  class " + className + " cluster ");
        for (ClusterChartDefinition clusterDef : inClusters) {
          sb.append(clusterDef.getClusterName());
          sb.append(", ");
        }
        sb.deleteCharAt(sb.length()-1);
        sb.deleteCharAt(sb.length()-1);
        
        sb.append(newLine);
        sb.append("  description");
        sb.append(newLine);
        sb.append("    ");
        sb.append(classDef.getExplanation());
        sb.append(newLine);
      }
    }

    sb.append("end");
    sb.append(newLine);
    sb.append(newLine);
    
    return sb.toString();
  }
  
}
