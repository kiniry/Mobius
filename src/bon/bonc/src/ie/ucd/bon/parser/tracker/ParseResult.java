/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.tracker;

import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.parser.BONParser;
import ie.ucd.bon.parser.BONParser.prog_return;
import ie.ucd.bon.parser.errors.ParsingError;

import java.io.File;

import org.antlr.runtime.CommonTokenStream;

/**
 * 
 * @author Fintan
 *
 */
public class ParseResult {

  private final boolean validParse;
  private final BONParser.prog_return parse;
  private final CommonTokenStream tokens;
  private final File file;
  private final Problems parseProblems;
  private final Problems lexerProblems;
  
  private final int severeProblemCount;
  
  public ParseResult(final boolean validParse, final prog_return parse, final CommonTokenStream tokens, final File file, final Problems problems, final Problems lexerProblems) {
    this.validParse = validParse;
    this.parse = parse;
    this.tokens = tokens;
    this.file = file;
    this.parseProblems = problems;
    this.lexerProblems = lexerProblems;
    
    this.severeProblemCount = countSevere(problems);
  }
  
  private static int countSevere(Problems problems) {
    int count = 0;
    for (BONProblem problem : problems.getProblems()) {
      if (problem.isError()) {
        if (((ParsingError)problem).isSevere()) {
          count++;
        }
      }
    }
    return count;
  }
  
  public boolean isValidParse() {
    return validParse;
  }

  public Problems getParseProblems() {
    return parseProblems;
  }
  
  public Problems getLexerProblems() {
    return lexerProblems;
  }

  public String getFilePath() {
    return file != null ? file.getPath() : "stdin";
  }
  
  public String getFileName() {
    return file != null ? file.getName() : "stdin";
  }
  
  public File getFile() {
    return file;
  }
  
  public BONParser.prog_return getParse() {
    return parse;
  }

  public CommonTokenStream getTokens() {
    return tokens;
  }

  public void addProblem(BONProblem problem) {
    parseProblems.addProblem(problem);
  }

  public int getSevereProblemCount() {
    return severeProblemCount;
  }
  
  public boolean continueFromParse(int safeNumberOfSevereParseErrors) {
    return severeProblemCount <= safeNumberOfSevereParseErrors;
  }
  

}
