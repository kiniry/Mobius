/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.FileNotFoundError;
import ie.ucd.bon.errorreporting.FileReadError;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.parser.BONLexer;
import ie.ucd.bon.parser.BONParser;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.typechecker.STBuilderVisitor;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.RewriteEarlyExitException;
import org.antlr.runtime.tree.RewriteEmptyStreamException;

/**
 *
 * @author Fintan
 *
 */
public final class Parser {

  //Keep static to save re-instantiating
  private static BONParser parser = new BONParser(null);
  private static BONLexer lexer = new BONLexer(null);

  /** Prevent instantiation of Parser. */
  private Parser() { }

  public static ParseResult parse(final File inputFile, final InputStream is) {
    if (is == null) {
      Problems problems = new Problems("Parser");
      problems.addProblem(new FileNotFoundError(inputFile));
      return new ParseResult(false, null, null, inputFile, problems, null);
    }
    if (inputFile != null) {
      Main.logDebug("Parsing " + inputFile.getPath());
    }
    CommonTokenStream tokens = null;
    BonSourceFile result = null;

    try {
      ANTLRInputStream input = new ANTLRInputStream(is);
      lexer.initialise(input, inputFile);
      tokens = new CommonTokenStream(lexer);
      parser.initialise(tokens, inputFile);
      result = parser.prog();
      is.close();
      Main.logDebug("Valid parse: " + parser.isValidParse());

      

      return new ParseResult(parser.isValidParse(), result, tokens, inputFile, parser.getProblems(), lexer.getProblems());

    } catch (IOException ioe) {
      BONProblem problem = new FileReadError(inputFile, ioe.getMessage());
      boolean valid = result != null; //Theoretically the IOException could be thrown closing the stream
      if (valid) {
        parser.getProblems().addProblem(problem);
        return new ParseResult(valid, result, tokens, inputFile, parser.getProblems(), null);
      } else {
        Problems problems = new Problems("Parser");
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
    } catch (RecognitionException re) {
      Main.logDebug("RecognitionException: " + re);
      if (Main.isDebug()) {
        re.printStackTrace(System.out);
      }
      return new ParseResult(false, null, null, inputFile, parser.getProblems(), null);
    }
  }
  
  public static void buildSymbolTable(ParseResult result, ParsingTracker tracker) {
    STBuilderVisitor v = new STBuilderVisitor(tracker.getSymbolTable());
    result.getParse().accept(v);
    result.setSTProblems(v.getProblems());
  }
}
