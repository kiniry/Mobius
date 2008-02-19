/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.tracker;

import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.typechecker.FormalTypeChecker;
import ie.ucd.bon.typechecker.TypingInformation;
import ie.ucd.bon.typechecker.informal.InformalTypeChecker;

import java.io.PrintStream;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

public class ParsingTracker {

  private final Vector<ParseResult> parses;
  private final Map<String,ParseResult> parsesMap;
  private final TypingInformation typingInformation;
  private final Problems problems;
  
  private FormalTypeChecker ftc;
  private InformalTypeChecker itc;
  
  private int severeProblemCount;
  private boolean containsFailedParses;
  
  private String finalMessage;
  
  public ParsingTracker() {
    parses = new Vector<ParseResult>(); 
    typingInformation = new TypingInformation();
    parsesMap = new HashMap<String,ParseResult>();
    problems = new Problems();
    
    severeProblemCount = 0;
    containsFailedParses = false;
    
    finalMessage = null;
    
    itc = null;
  }

  public Collection<ParseResult> getParses() {
    return parses;
  }
  
  public ParseResult getParseResult(String fileName) {
    if (fileName.equals("-")) {
      return parsesMap.get("stdin");
    }
    return parsesMap.get(fileName);
  }
  
  public void addParse(String fileName, ParseResult parse) {
    parses.add(parse);
    parsesMap.put(fileName, parse);
    
    severeProblemCount += parse.getSevereProblemCount();
    if (!parse.isValidParse()) {
      containsFailedParses = true;
    }
  }

  public TypingInformation getTypingInformation() {
    return typingInformation;
  }

  public void addProblem(BONProblem problem) {
    problems.addProblem(problem);
  }
  
  public void setFinalMessage(String finalMessage) {
    this.finalMessage = finalMessage;
  }
  
  public Problems getErrorsAndWarnings(boolean checkInformal, boolean checkFormal, boolean checkConsistency) {
    //TODO provide filter level and filter...
    
    Problems probs = new Problems();
    probs.addProblems(this.problems);
    
    probs.addProblems(typingInformation.getProblems());
    
    probs.addProblems(typingInformation.informal().getProblems());
    
    if (checkInformal && itc != null) {
      probs.addProblems(itc.getProblems());
    }
    
    if (checkFormal && ftc != null) {
      probs.addProblems(ftc.getProblems());
    }
    
    if (checkConsistency && ftc != null) {
      probs.addProblems(ftc.getConsistencyProblems());
    }
    
    for (ParseResult parse : parses) {
      probs.addProblems(parse.getParseProblems());
      Problems lexerProblems = parse.getLexerProblems();
      if (lexerProblems != null) {
        probs.addProblems(lexerProblems);
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
  
  public InformalTypeChecker getInformalTypeChecker() {
    if (itc == null) {
      itc = typingInformation.informal().getInformalTypeChecker();
    }
    return itc;
  }
  
  public FormalTypeChecker getFormalTypeChecker() {
    if (ftc == null) {
      ftc = typingInformation.getFormalTypeChecker();
    }
    return ftc;
  }
}
