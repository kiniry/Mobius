/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser;

import ie.ucd.bon.Main;

import java.util.HashMap;
import java.util.Map;

public class ParseProblemExplanations {

  public static String getExplanation(Throwable t) {
    String methodName = getThrowingMethodName(t);
    Main.logDebug("Method name: " + methodName);
    if (methodName != null) {
      return getExplanationForMethodName(methodName, t);
    } else {
      return null;
    }
  }
  
  public static String getExplanationWithExpecting(Throwable t, String expecting) {
    String methodName = getThrowingMethodName(t);
    Main.logDebug("Method name: " + methodName + ", expecting " + expecting);
    if (methodName != null) {
      return getExplanationForMethodNameWithExpecting(methodName, t, expecting);
    } else {
      return null;
    }
  }
  
  private static String getThrowingMethodName(Throwable t) {
    StackTraceElement[] stackTrace = t.getStackTrace();
    if (stackTrace != null) {
      for (StackTraceElement trace : stackTrace) {
        if (trace.getClassName().equals(BONParser.class.getName())) {
          Main.logDebug("Matched: " + trace.getClassName() + "." + trace.getMethodName());
          return trace.getMethodName();
        }
      }
      Main.logDebug("No ie.ucd stack trace element for throwable " + t);
      return null;
    } else {
      Main.logDebug("No stack trace for throwable " + t);
      return null;
    }
  }
  
  private static final String getExplanationForMethodName(String methodName, Throwable t) {
    if (explanationMap == null) {
      initialiseExplanationMap();
    }
    return explanationMap.get(t.getClass().getName() + '*' + methodName);
  }
  
  private static final String getExplanationForMethodNameWithExpecting(String methodName, Throwable t, String expecting) {
    if (explanationMap == null) {
      initialiseExplanationMap();
    }
    return explanationMap.get(t.getClass().getName() + '*' + methodName + '*' + expecting);
  }
  
  private static Map<String,String> explanationMap;
  
  private static final void initialiseExplanationMap() {
    explanationMap = new HashMap<String,String>();
    
    //Currently a single (optional) placeholder for the unexpected input.
    
    explanationMap.put("org.antlr.runtime.NoViableAltException*prog", "Expecting system_chart, cluster_chart, class_chart, event_chart, scenario_chart, creation_chart, dictionary, static_diagram, or dynamic_diagram");
    
    explanationMap.put("org.antlr.runtime.MismatchedTokenException*prog*EOF", "Expecting system_chart, cluster_chart, class_chart, event_chart, scenario_chart, creation_chart, dictionary, static_diagram, or dynamic_diagram");
    explanationMap.put("org.antlr.runtime.MismatchedTokenException*class_name*IDENTIFIER", "Unexpected input %s, expecting class name");
    explanationMap.put("org.antlr.runtime.MismatchedTokenException*cluster_name*IDENTIFIER", "Unexpected input %s, expecting cluster name");
    explanationMap.put("org.antlr.runtime.MismatchedTokenException*system_name*IDENTIFIER", "Unexpected input %s, expecting system name");
  } 

  
}
