/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.BONType;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.source.SourceLocation;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import org.antlr.runtime.Token;

public final class Context {

  //Informal
  private boolean inSystemChart;
  private boolean inClusterChart;
  private String clusterChartName;
  private boolean inClassChart;
  private String classChartName;
  private boolean inInheritsClause;
  private boolean inEventEntry;
  private boolean inCreationEntry;
  private boolean inClassEntry;
  private String classEntryName;
  
  private boolean inDictionaryEntry;
  private String dictionaryEntryClassName;
  private Token dictionaryEntryStartToken;
  
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
  private ClientRelation clientRelation;
  private boolean inClientRelation;
  
  //Expressions
  private final Stack<BONType> typeStack;
  private BONType lastType;
  private final Stack<Map<String,BONType>> quantificationStack;
    
  private static final Context instance = new Context(); 
  
  private Context() {
    clusterStack = new Stack<String>();
    typeStack = new Stack<BONType>();
    quantificationStack = new Stack<Map<String,BONType>>();
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
    inClassEntry = false;
    classEntryName = null;
    
    inDictionaryEntry = false;
    dictionaryEntryClassName = null;
    
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
  
  public void enterDictionaryEntry(String className, Token startToken) {
    inDictionaryEntry = true;
    dictionaryEntryClassName = className;
    dictionaryEntryStartToken = startToken;
  }
  
  public void leaveDictionaryEntry() {
    inDictionaryEntry = false;
    dictionaryEntryClassName = null;
    dictionaryEntryStartToken = null;
  }
  
  public boolean isInDictionaryEntry() {
    return inDictionaryEntry;
  }
  
  public String getDictionaryEntryClassName() {
    return dictionaryEntryClassName;
  }
  
  public Token getDictionaryEntryStartToken() {
    return dictionaryEntryStartToken;
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
  
  

  public boolean isInClassChart() {
    return inClassChart;
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
  public void addTypeRequirement(BONType type) {
    typeStack.add(type);
  }
  
  public void removeTypeRequirement() {
    typeStack.pop();
  }
  
  public BONType currentTypeRequirement() {
    return typeStack.empty() ? null : typeStack.peek();
  }
  
  public void setLastCallChainType(BONType t) {
    lastType = t;
  }
  
  public BONType getLastCallChainType() {
    return lastType;
  }
  
  public void clearLastCallChainType() {
    lastType = null;
  }
  
  public void enterQuantification() {
    quantificationStack.push(new HashMap<String,BONType>());
  }
  
  public void leaveQuantification() {
    quantificationStack.pop();
  }
  
  public Stack<Map<String,BONType>> getQuantificationStack() {
    return quantificationStack;
  }

  public boolean isInClassEntry() {
    return inClassEntry;
  }

  public String getClassEntryName() {
    return classEntryName;
  }
  
  public void enterClassEntry(String classEntryName) {
    inClassEntry = true;
    this.classEntryName = classEntryName;
  }
  
  public void leaveClassEntry() {
    inClassEntry = false;
    this.classEntryName = null;
  }
  
  public void enterClientRelation(ClientRelation cr) {
    inClientRelation = true;
    clientRelation = cr;
  }
  
  public void leaveClientRelation() {
    inClientRelation = false;
  }

  public ClientRelation getClientRelation() {
    return clientRelation;
  }

  public boolean isInClientRelation() {
    return inClientRelation;
  }
  
}
