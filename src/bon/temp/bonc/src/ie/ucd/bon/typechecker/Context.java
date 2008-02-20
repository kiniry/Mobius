/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.parser.SourceLocation;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import org.antlr.runtime.Token;

public class Context {

  //Informal
  private boolean inSystemChart;
  private boolean inClusterChart;
  private String clusterChartName;
  private boolean inClassChart;
  private String classChartName;
  private boolean inInheritsClause;
  private boolean inEventEntry;
  private boolean inCreationEntry;
  
  //Static diagrams
  private boolean inClass;
  private boolean inCluster;
  private String className;
  private final Stack<String> clusterStack;  
  private boolean inFeatureClause;
  private Feature feature;
  private boolean inFeatureSpecification;
  private FeatureSpecification featureSpec;
  private boolean inSelectiveExport;
  
  //Expressions
  private final Stack<Type> typeStack;
  private Type lastType;
  private final Stack<Map<String,Type>> quantificationStack;
  
  private static final Context instance = new Context(); 
  
  private Context() {
    clusterStack = new Stack<String>();
    typeStack = new Stack<Type>();
    quantificationStack = new Stack<Map<String,Type>>();
    reset(); 
  }
  
  public static Context getContext() {
    return instance;
  }
  
  public final void reset() {
    inSystemChart = false;
    inClusterChart = false;
    clusterChartName = null;
    inClassChart = false;
    classChartName = null;
    inInheritsClause = false;
    inEventEntry = false;
    inCreationEntry = false;
    
    inClass = false;
    inCluster = false;
    className = null;
    clusterStack.clear();
    inFeatureClause = false;
    feature = null;
    inFeatureSpecification = false;
    featureSpec = null;
    inSelectiveExport = false;
    typeStack.clear();
    lastType = null;
    quantificationStack.clear();

  }
  
  public void enterSystemChart(String systemName) {
    enterClusterChart(systemName);
    inSystemChart = true;
  }
  
  public void leaveSystemChart() {
    leaveClusterChart();
    inSystemChart = false;
  }
   
  public boolean isInSystemChart() {
    return inSystemChart;
  }

  public void enterClusterChart(String clusterName) {
    inClusterChart = true;
    this.clusterChartName = clusterName; 
  }
  
  public void leaveClusterChart() {
    inClusterChart = false;
    this.clusterChartName = null;
  }
  
  public boolean isInClusterChart() {
    return inClusterChart;
  }

  public void enterClassChart(String className) {
    inClassChart = true;
    this.classChartName = className;
  }
  
  public void leaveClassChart() {
    inClassChart = false;
    this.classChartName = null;
  }

  public String getClusterChartName() {
    return clusterChartName;
  }

  public String getClassChartName() {
    return classChartName;
  }
  
  public void enterInheritsClause() {
    inInheritsClause = true;
  }
  
  public void leaveInheritsClause() {
    inInheritsClause = false;
  }  
  
  public boolean isInInheritsClause() {
    return inInheritsClause;
  }
  
  public void enterCluster(String clusterName) {
    //TODO push cluster we are in onto stack...
    inCluster = true;
    clusterStack.push(clusterName);
  }
  
  public void leaveCluster() {
    //pop top-most cluster from stack.
    clusterStack.pop();
    //If no clusters left in stack, inCluster = false;
    inCluster = !clusterStack.empty();
  }
  
  public void enterClass(String className) {
    inClass = true;
    this.className = className;
  }
  
  public void leaveClass() {
    inClass = false;
    className = null;
  }

//  public File getSourceFile() {
//    return sourceFile;
//  }

  public boolean isInClass() {
    return inClass;
  }

  public String getClassName() {
    return className;
  }

  public boolean isInCluster() {
    return inCluster;
  }
  
  public String getInnermostCluster() {
    return clusterStack.empty() ? null : clusterStack.peek();
  }
  
  public void enterFeatureClause(SourceLocation loc) {
    inFeatureClause = true;
    feature = new Feature(loc, className);
  }
  
  public void leaveFeatureClause() {
    inFeatureClause = false;
    feature = null;
  }
  
  public Feature getFeature() {
    return feature;
  }
  
  public void enterFeatureSpecification() {
    inFeatureSpecification = true;
    featureSpec = new FeatureSpecification(feature);
  }
  
  public void leaveFeatureSpecification() {
    inFeatureSpecification = false;
    featureSpec = null;
  }

  public boolean isInFeatureSpecification() {
    return inFeatureSpecification;
  }

  public FeatureSpecification getFeatureSpec() {
    return featureSpec;
  }
  
  public void enterSelectiveExport() {
    inSelectiveExport = true;
  }
  
  public void leaveSelectiveExport() {
    inSelectiveExport = false;
  }

  public boolean isInSelectiveExport() {
    return inSelectiveExport;
  }
  
  public void enterEventEntry() {
    inEventEntry = true;
  }
  
  public void leaveEventEntry() {
    inEventEntry = false;
  }
  
  public boolean isInEventEntry() {
    return inEventEntry;
  }
  
  public void enterCreationEntry() {
    inCreationEntry = true;
  }
  
  public void leaveCreationEntry() {
    inCreationEntry = false;
  }
  
  public boolean isInCreationEntry() {
    return inCreationEntry;
  }
  
  //Expressions
  public void addTypeRequirement(Type type) {
    typeStack.add(type);
  }
  
  public void removeTypeRequirement() {
    typeStack.pop();
  }
  
  public Type currentTypeRequirement() {
    return typeStack.empty() ? null : typeStack.peek();
  }
  
  public void setLastCallChainType(Type t) {
    lastType = t;
  }
  
  public Type getLastCallChainType() {
    return lastType;
  }
  
  public void clearLastCallChainType() {
    lastType = null;
  }
  
  public void enterQuantification() {
    quantificationStack.push(new HashMap<String,Type>());
  }
  
  public void leaveQuantification() {
    quantificationStack.pop();
  }
  
  public Stack<Map<String,Type>> getQuantificationStack() {
    return quantificationStack;
  }
  
}
