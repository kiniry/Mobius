/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.tracker;

import ie.ucd.bon.Parser;
import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.typechecker.BONST;
import ie.ucd.bon.util.FileUtil;

import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

public class ParsingTracker {

  public static final String FAKE_BUILTIN_FILENAME = "<built-in>";
  
  private ParseResult stdParse;
  private final ParseResult builtInParse;
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
    
    builtInParse = Parser.parse(new File(FAKE_BUILTIN_FILENAME), FileUtil.getInputStream("src/builtin/built_in.bon"));
    Parser.buildSymbolTable(builtInParse, this);
  }

  public Collection<ParseResult> getParses() {
    return parses;
  }
  
  public Collection<ParseResult> getParsesIncludingBuiltIn() {
    Collection<ParseResult> allParses = new ArrayList<ParseResult>(parses.size() + 1);
    allParses.add(builtInParse);
    return allParses;
  }

  public ParseResult getParseResult(File file) {
    if (file == null) {
      return stdParse;
    }
    return parsesMap.get(file);
  }

  public void addParse(File file, ParseResult parse) {
    parsesMap.put(file, parse);
    addParse(parse);
  }
  
  public void addStdParse(ParseResult stdParse) {
    this.stdParse = stdParse;
    addParse(stdParse);
  }
  
  private void addParse(ParseResult parse) {
    parses.add(parse);
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

  public boolean continueFromParse() {
    return containsFailedParses ? false : severeProblemCount == 0;
  }

  public BONST getSymbolTable() {
    return symbolTable;
  }
}
