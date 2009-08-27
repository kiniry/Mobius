/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.tracker;

import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.typechecker.BONST;

import java.io.File;
import java.io.PrintStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

public class ParsingTracker {

  private ParseResult stdParse;
  private final Vector<ParseResult> parses;
  private final Map<File,ParseResult> parsesMap;
  private final Problems problems;
  
  private int severeProblemCount;
  private boolean containsFailedParses;
  
  private BONST symbolTable;
  
  private String finalMessage;
  
  public ParsingTracker() {
    parses = new Vector<ParseResult>(); 
    parsesMap = new HashMap<File,ParseResult>();
    problems = new Problems("Tracker");
    
    severeProblemCount = 0;
    containsFailedParses = false;
    
    finalMessage = null;
    
    symbolTable = new BONST();
  }

  public Collection<ParseResult> getParses() {
    return parses;
  }
  
  public ParseResult getParseResult(File file) {
    if (file == null) {
      return stdParse;
    }
    return parsesMap.get(file);
  }
  
  public void addParse(File file, ParseResult parse) {
    parses.add(parse);
    if (file == null) {
      stdParse = parse;
    } else {
      parsesMap.put(file, parse);
    }
    
    severeProblemCount += parse.getSevereProblemCount();
    if (!parse.isValidParse()) {
      containsFailedParses = true;
    }
  }

  public void addProblem(BONProblem problem) {
    problems.addProblem(problem);
  }
  
  public void addProblems(Problems newProblems) {
    problems.addProblems(newProblems);
  }

  public void setFinalMessage(String finalMessage) {
    this.finalMessage = finalMessage;
  }
  
  public Problems getErrorsAndWarnings() {
    //TODO provide filter level and filter...    
    Problems probs = new Problems("Return");
    probs.addProblems(this.problems);
    
    for (ParseResult parse : parses) {
      probs.addProblems(parse.getParseProblems());
      Problems lexerProblems = parse.getLexerProblems();
      if (lexerProblems != null) {
        probs.addProblems(lexerProblems);
      }
      Problems stProblems = parse.getStProblems();
      if (stProblems != null) {
        probs.addProblems(stProblems);
      }
    }
    return probs;
  }
  
  public void printFinalMessage(PrintStream ps) {        
    if (finalMessage != null) {
      ps.println(finalMessage);
    }
  }
  
  
  public boolean continueFromParse(int safeNumberOfSevereParseErrors) {
    return containsFailedParses ? false : severeProblemCount <= safeNumberOfSevereParseErrors;
  }

  public BONST getSymbolTable() {
    return symbolTable;
  }
  
  

}
