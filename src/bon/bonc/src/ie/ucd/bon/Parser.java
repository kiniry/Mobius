/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.FileNotFoundError;
import ie.ucd.bon.errorreporting.FileReadError;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.parser.BONLexer;
import ie.ucd.bon.parser.BONParser;
import ie.ucd.bon.parser.SourceReader;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.RewriteEarlyExitException;
import org.antlr.runtime.tree.RewriteEmptyStreamException;

/**
 * 
 * @author Fintan
 *
 */
public class Parser {
  
  private static BONParser parser = new BONParser(null);
  private static BONLexer lexer = new BONLexer(null);
  
  public static ParseResult parse(File inputFile, ParsingTracker tracker) 
  throws RecognitionException {
    if (inputFile != null) {
      Main.logDebug("Parsing " + inputFile.getPath());
    }
    CommonTokenStream tokens = null;
    BONParser.prog_return result = null;

    try {
      ANTLRInputStream input;
      if (inputFile != null) {
        FileInputStream fis = new FileInputStream(inputFile);
        input = new ANTLRInputStream(fis);
        //EBONLexer lexer = new EBONLexer(input);
        lexer.initialise(input, inputFile);
        tokens = new CommonTokenStream(lexer);
        parser.initialise(tracker, tokens, inputFile);
        result = parser.prog();
        fis.close();
        Main.logDebug("Valid parse: " + parser.isValidParse());
        return new ParseResult(parser.isValidParse(), result, tokens, inputFile, parser.getProblems(), lexer.getProblems());
      } else {
        input = new ANTLRInputStream(SourceReader.getInstance().readStandardInput());
        //EBONLexer lexer = new EBONLexer(input);
        lexer.initialise(input, null);
        tokens = new CommonTokenStream(lexer);
        parser.initialise(tracker, tokens, null);
        result = parser.prog();
        Main.logDebug("Valid parse: " + parser.isValidParse());
        return new ParseResult(parser.isValidParse(), result, tokens, null, parser.getProblems(), lexer.getProblems());
      }
      
    } catch (FileNotFoundException fnfe) {
      Problems problems = new Problems();
      problems.addProblem(new FileNotFoundError(inputFile));
      return new ParseResult(false, null, null, inputFile, problems, null);
    } catch (IOException ioe) {
      BONProblem problem = new FileReadError(inputFile, ioe.getMessage());
      boolean valid = result != null; //Theoretically the IOException could be thrown closing the stream
      if (valid) {
        parser.getProblems().addProblem(problem);
        return new ParseResult(valid, result, tokens, inputFile, parser.getProblems(), null);
      } else {
        Problems problems = new Problems();
        problems.addProblem(problem);
        return new ParseResult(false, null, null, inputFile, problems, null);
      }
    } catch (RewriteEmptyStreamException rese) {
      Main.logDebug("RewriteEmptyStreamException: " + rese);
      if (Main.isDebug()) {
        rese.printStackTrace(System.out);
      }
      return new ParseResult(false, null, null, inputFile, parser.getProblems(), null);
    } catch (RewriteEarlyExitException reee) {
      Main.logDebug("RewriteEmptyStreamException: " + reee);
      if (Main.isDebug()) {
        reee.printStackTrace(System.out);
      }
      return new ParseResult(false, null, null, inputFile, parser.getProblems(), null);
    }
  }
}
