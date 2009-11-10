/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser;

import ie.ucd.bon.Main;
import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.parser.errors.AntlrParsingError;
import ie.ucd.bon.parser.errors.ParsingError;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.NullIgnoringList;
import ie.ucd.bon.util.NullOutputStream;

import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.antlr.runtime.BitSet;
import org.antlr.runtime.EarlyExitException;
import org.antlr.runtime.FailedPredicateException;
import org.antlr.runtime.IntStream;
import org.antlr.runtime.MismatchedNotSetException;
import org.antlr.runtime.MismatchedSetException;
import org.antlr.runtime.MismatchedTokenException;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.Parser;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenStream;

/**
 * @author Fintan
 */
public abstract class AbstractBONParser extends Parser {

  private boolean validParse;
  private File sourceFile;
  private Problems problems;

  public AbstractBONParser(TokenStream input, RecognizerSharedState state) {
    super(null, state);
  }

  /**
   * {@inheritDoc}
   */
  public void initialise(TokenStream input, File sourceFile) {
    this.sourceFile = sourceFile;
    validParse = true;
    problems = new Problems("Parser");
    super.setTokenStream(input);
  }

  /**
   * Get the name for the token type given.
   * @param tokenType The token type to get the name for.
   * @return The name of the given token type.
   */
  public String getTokenTypeName(int tokenType) {
    String[] tokenNames = getTokenNames();
    if (tokenType < tokenNames.length && tokenType >= 0) {
      return tokenNames[tokenType];
    } else {
      return "***INVALID TOKEN TYPE***";
    }
  }



  @Override
  public boolean mismatchIsMissingToken(IntStream input, BitSet follow) {
    Main.logDebug("Mismatch (missing token).");
    return super.mismatchIsMissingToken(input, follow);
  }

  @Override
  public boolean mismatchIsUnwantedToken(IntStream input, int ttype) {
    Main.logDebug("Mismatch (unwanted token).");
    return super.mismatchIsUnwantedToken(input, ttype);
  }

  /**
   * {@inheritDoc}
   */
  public boolean isValidParse() {
    return validParse;
  }

  //TODO what is the difference between tokenNames here and getTokenNames()
  public BONProblem getErrorProblem(RecognitionException e, String[] tokenNames) {
    if (e instanceof MismatchedTokenException) {
      MismatchedTokenException mte = (MismatchedTokenException)e;

      String tokenName;
      if (mte.expecting == Token.EOF) {
        tokenName = "EOF";
      } else {
        tokenName = tokenNames[mte.expecting];
      }

      if (e.token.getType() == Token.EOF) {
        Token t = input.LT(-1);
        if (t != null) {
          String prevTokenText = t.getText();
          String msg = "Expected " + tokenName + " after " + prevTokenText + ", before end of file";
          //return new AntlrParsingError(sourceFile, t.getLine(), t.getCharPositionInLine()+prevTokenText.length()+1, msg, true);
          return new AntlrParsingError(new SourceLocation(t, e.token, sourceFile), msg, true);
        } else {
          String msg = "Unexpected input " + getTokenErrorDisplay(e.token) + ", expecting " + tokenName + "";
          //return new AntlrParsingError(sourceFile, BONProblem.EOF_LINE, 0, msg, true);
          return new AntlrParsingError(new SourceLocation(e.token, sourceFile), msg, true);
        }
      } else {
        //Main.logDebug("Mismatched " + getTokenErrorDisplay(e.token) + ", expecting " + tokenName);
        String msg = ParseProblemExplanations.getExplanationWithExpecting(e,tokenName);

        if (msg == null) {
          msg = "Unexpected input " + getTokenErrorDisplay(e.token) + ", expecting " + tokenName + "";
        } else {
          msg = String.format(msg, getTokenErrorDisplay(e.token));
        }
        //return new AntlrParsingError(sourceFile, e.line, e.charPositionInLine, msg, true);
        return new AntlrParsingError(new SourceLocation(e.token, sourceFile), msg, true);
      }

    } else if (e instanceof NoViableAltException) {
      String msg = ParseProblemExplanations.getExplanation(e);
      if (msg == null) {
        msg = "Unexpected input " + getTokenErrorDisplay(e.token);
      }
      //return new AntlrParsingError(sourceFile, e.line, e.charPositionInLine, msg, true);
      return new AntlrParsingError(new SourceLocation(e.token, sourceFile), msg, true);

    } else if (e instanceof EarlyExitException) {
      String explanation = ParseProblemExplanations.getExplanation(e);

      String msg;
      if (explanation != null) {
        msg = "Missing " + explanation;
      } else {
        //Main.logDebug("Debug: could not find explanation for EarlyExitException from method " + methodName);
        //msg = "required (...)+ loop did not match anything at input "+ getTokenErrorDisplay(e.token);
        msg = "Unexpected input "+ getTokenErrorDisplay(e.token);
      }
      //return new AntlrParsingError(sourceFile, e.line, e.charPositionInLine, msg, true);
      return new AntlrParsingError(new SourceLocation(e.token, sourceFile), msg, true);

    } else if (e instanceof MismatchedSetException) {
      MismatchedSetException mse = (MismatchedSetException)e;
      String msg = "mismatched input "+getTokenErrorDisplay(e.token)+" expecting set "+mse.expecting;
      //return new AntlrParsingError(sourceFile, e.line, e.charPositionInLine, msg, true);
      return new AntlrParsingError(new SourceLocation(e.token, sourceFile), msg, true);
    } else if (e instanceof MismatchedNotSetException) {
      MismatchedNotSetException mse = (MismatchedNotSetException)e;
      String msg = "mismatched input "+getTokenErrorDisplay(e.token)+" expecting set "+mse.expecting;
      //return new AntlrParsingError(sourceFile, e.line, e.charPositionInLine, msg, true);
      return new AntlrParsingError(new SourceLocation(e.token, sourceFile), msg, true);
    } else if (e instanceof FailedPredicateException) {
      FailedPredicateException fpe = (FailedPredicateException)e;
      String msg = "rule "+fpe.ruleName+" failed predicate: {"+fpe.predicateText+"}?";
      //return new AntlrParsingError(sourceFile, e.line, e.charPositionInLine, msg, true);
      return new AntlrParsingError(new SourceLocation(e.token, sourceFile), msg, true);
    } else {
      //return new AntlrParsingError(sourceFile, e.line, e.charPositionInLine, "An unknown error occurred", true);
      return new AntlrParsingError(new SourceLocation(e.token, sourceFile), "An unknown error occurred", true);
    }

  }

  /**
   * Returns the error header, which is just the source filename and the line number on
   * which the error occurs.
   *
   * @param e The RecognitionException representing the error
   * @return A String giving the source filename and line on which the error occurs
   */
  public String getErrorHeader(RecognitionException e) {
    return null; //sourceFileName + ":" + e.line + ":";
  }

  /**
   * Get a string to identify this Token for use in an error message.
   * @param t the Token to identify.
   * @return a String to identify the provided token in an error message.
   */
  public String getTokenErrorDisplay(Token t) {
    String s = t.getText();
    if (s == null) {
      if (t.getType() == Token.EOF) {
        s = "<EOF>";
      } else {
        s = "<"+t.getType()+">";
      }
    }
    s = s.replaceAll("\n","\\\\n");
    s = s.replaceAll("\r","\\\\r");
    s = s.replaceAll("\t","\\\\t");
    return "'" + s + "'";
  }

  public void displayRecognitionError(String[] tokenNames, RecognitionException e) {
    BONProblem problem = getErrorProblem(e, tokenNames);

    Main.logDebug("Recognition error (" + e.getClass().getName() + "): " + problem.getMessage());
    Main.logDebug("Stack trace: ");
    if (Main.isDebug()) {
      e.printStackTrace(System.out);
    }

    validParse = false;

    //TODO adjust severity here according to if we recovered ok or not...
    problems.addProblem(problem);
  }

  @Override
  public void recover(IntStream input, RecognitionException re) {
    Main.logDebug("Recovering..." + re);
    PrintStream oldErr = System.err;
    System.setErr(NullOutputStream.getNullPrintStreamInstance());
    super.recover(input, re);
    System.setErr(oldErr);
  }

  @Override
  public Object recoverFromMismatchedSet(IntStream input,
      RecognitionException e, BitSet follow) throws RecognitionException {
    Main.logDebug("Recovering from mismatched set..." + e);
    PrintStream oldErr = System.err;
    System.setErr(NullOutputStream.getNullPrintStreamInstance());
    Object result = super.recoverFromMismatchedSet(input, e, follow);
    System.setErr(oldErr);
    return result;
  }

  @Override
  protected Object recoverFromMismatchedToken(IntStream arg0, int arg1, BitSet arg2) throws RecognitionException {
    Main.logDebug("Recovering from mismatched token...");
    PrintStream oldErr = System.err;
    System.setErr(NullOutputStream.getNullPrintStreamInstance());
    Object result = super.recoverFromMismatchedToken(arg0, arg1, arg2);
    System.setErr(oldErr);
    return result;
  }

  public final SourceLocation getSourceLocation(Token t) {
    return new SourceLocation(t, this.sourceFile);
  }

  public final SourceLocation getSourceLocation(Token tStart, Token tEnd) {
    return new SourceLocation(tStart, tEnd, this.sourceFile);
  }

  //Just a shorter version
  public final SourceLocation getSLoc(Token t) {
    return getSourceLocation(t);
  }

  //Just a shorter version
  public final SourceLocation getSLoc(Token tStart, Token tEnd) {
    return getSourceLocation(tStart, tEnd);
  }

  public final SourceLocation getSLoc(SourceLocation start, SourceLocation end) {
    return new SourceLocation(start, end);
  }

  public final void addParseProblem(BONProblem problem) {
    if (problem instanceof ParsingError) {
      if (((ParsingError)problem).isSevere()) {
        validParse = false;
      }
    }
    problems.addProblem(problem);
  }

  public Problems getProblems() {
    return problems;
  }

  protected static <T> List<T> createList() {
    //return new LinkedList<T>();
    return new NullIgnoringList<T>(new ArrayList<T>());
  }

  protected static <T> List<T> emptyList() {
    return Collections.emptyList();
  }

}
