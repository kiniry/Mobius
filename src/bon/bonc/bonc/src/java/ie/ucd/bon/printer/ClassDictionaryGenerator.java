/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.printer;

import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.graph.Graph;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.BONST;

import java.util.Collection;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

public final class ClassDictionaryGenerator {

  /** Private constructor, disallow instantiation. */
  private ClassDictionaryGenerator() { }

  public static String generateDictionary(ParsingTracker tracker) throws UnableToGenerateClassDictionaryException {
    String newLine = System.getProperty("line.separator");

    StringBuilder sb = new StringBuilder();

    BONST st = tracker.getSymbolTable();

    ClusterChart sys = st.informal.systemChart;
    Map<String,ClassChart> classes = st.informal.classes;
    SortedSet<String> classNames = new TreeSet<String>(classes.keySet());
    Graph<String, ClusterChart> classClusterGraph = st.informal.classClusterGraph;

    if (sys == null) {
      throw new UnableToGenerateClassDictionaryException("No system defined!");
    }
    if (classNames.size() == 0) {
      throw new UnableToGenerateClassDictionaryException("No classes in system!");
    }

    sb.append("dictionary ");
    sb.append(sys.getName());
    sb.append(newLine);

    sb.append("  explanation");
    sb.append(newLine);
    sb.append("    \"BONc automatically generated class dictionary.\"");
    sb.append(newLine);

    for (String className : classNames) {
      ClassChart classDef = classes.get(className);

      Collection<ClusterChart> inClusters = classClusterGraph.get(className);
      if (inClusters == null || inClusters.size() == 0) {
        //TODO or just ignore?
        throw new UnableToGenerateClassDictionaryException("Class " + className + " is not in any cluster!");
      } else {
        sb.append("  class " + className + " cluster ");
        for (ClusterChart clusterDef : inClusters) {
          sb.append(clusterDef.getName());
          sb.append(", ");
        }
        sb.deleteCharAt(sb.length()-1);
        sb.deleteCharAt(sb.length()-1);

        sb.append(newLine);
        sb.append("  description");
        sb.append(newLine);
        sb.append("    ");
        if (classDef.getExplanation() == null || "".equals(classDef.getExplanation())) {
          String altDesc = st.informal.alternativeClassDescriptions.get(className);
          sb.append(altDesc == null ? "" : altDesc);
        } else {
          sb.append(classDef.getExplanation());
        }
        sb.append(newLine);
      }
    }

    sb.append("end");
    sb.append(newLine);
    sb.append(newLine);

    return sb.toString();
  }

}
