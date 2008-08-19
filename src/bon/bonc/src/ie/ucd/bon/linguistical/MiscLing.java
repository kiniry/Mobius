/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.linguistical;

import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.informal.ClassChartDefinition;

import java.util.Collection;

public class MiscLing {

  public static String printClassChartSentences(ParsingTracker tracker) {
    Collection<ClassChartDefinition> classes = tracker.getInformalTypingInformation().getClasses().values();
    StringBuilder sb = new StringBuilder();
    
    for (ClassChartDefinition def : classes) {
      Collection<String> queries = def.getQueries();
      for (String query : queries) {
        sb.append(query.substring(1, query.length()-1));
        sb.append('\n');
      }
      
      Collection<String> commands = def.getCommands();
      for (String command : commands) {
        sb.append(command.substring(1, command.length()-1));
        sb.append('\n');
      }
      
      Collection<String> constraints = def.getConstraints();
      for (String constraint : constraints) {
        sb.append(constraint.substring(1, constraint.length()-1));
        sb.append('\n');
      }
    }
    
    return sb.toString();
  }
  
  
  
}
