/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser;

import ie.ucd.bon.Main;
import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.parser.errors.AntlrParsingError;
import ie.ucd.bon.source.SourceLocation;

import java.io.File;

import org.antlr.runtime.CharStream;
import org.antlr.runtime.EarlyExitException;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.MismatchedNotSetException;
import org.antlr.runtime.MismatchedRangeException;
import org.antlr.runtime.MismatchedSetException;
import org.antlr.runtime.MismatchedTokenException;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.RecognitionException;

public abstract class AbstractBONLexer extends Lexer {

  private File sourceFile;
  private Problems problems;

  public AbstractBONLexer() {
  }

  public AbstractBONLexer(CharStream input) {
    super(null);
  }

  public void initialise(CharStream input, File sourceFile) {
    super.input = input;
    this.sourceFile = sourceFile;
    problems = new Problems();
    super.reset();
  }

  @Override
  public abstract void mTokens() throws RecognitionException;

  @Override
  public String getErrorMessage(RecognitionException e, String[] tokenNames) {
    String msg = null;
    if ( e instanceof MismatchedTokenException ) {
      MismatchedTokenException mte = (MismatchedTokenException)e;
      msg = "Unexpected character "+getCharErrorDisplay(e.c)+", expecting "+getCharErrorDisplay(mte.expecting);
    }
    else if ( e instanceof NoViableAltException ) {
      NoViableAltException nvae = (NoViableAltException)e;
      // for development, can add "decision=<<"+nvae.grammarDecisionDescription+">>"
      // and "(decision="+nvae.decisionNumber+") and
      // "state "+nvae.stateNumber
      msg = "Unexpected input at character "+getCharErrorDisplay(e.c);
    }
    else if ( e instanceof EarlyExitException ) {
      EarlyExitException eee = (EarlyExitException)e;
      // for development, can add "(decision="+eee.decisionNumber+")"
      msg = "required (...)+ loop did not match anything at character "+getCharErrorDisplay(e.c);
    }
    else if ( e instanceof MismatchedNotSetException ) {
      MismatchedNotSetException mse = (MismatchedNotSetException)e;
      msg = "mismatched character "+getCharErrorDisplay(e.c)+" expecting set "+mse.expecting;
    }
    else if ( e instanceof MismatchedSetException ) {
      MismatchedSetException mse = (MismatchedSetException)e;
      msg = "mismatched character "+getCharErrorDisplay(e.c)+" expecting set "+mse.expecting;
    }
    else if ( e instanceof MismatchedRangeException ) {
      MismatchedRangeException mre = (MismatchedRangeException)e;
      msg = "mismatched character "+getCharErrorDisplay(e.c)+" expecting set "+
      getCharErrorDisplay(mre.a)+".."+getCharErrorDisplay(mre.b);
    }
    else {
      msg = super.getErrorMessage(e, tokenNames);
    }
    return msg;
  }

  public String getErrorHeader(RecognitionException e) {
    return null;
  }

  public void displayRecognitionError(String[] tokenNames, RecognitionException e) {
    //String hdr = getErrorHeader(e);
    String msg = getErrorMessage(e, tokenNames);
    //emitErrorMessage(hdr+" "+msg);
    Main.logDebug("Lexer Recognition error (" + e.getClass().getName() + "): " + msg);
    if (Main.isDebug()) {
      e.printStackTrace(System.out);
    }

    BONProblem problem = new AntlrParsingError(new SourceLocation(e.token, sourceFile), msg, true);
    //BONProblem problem = new AntlrParsingError(sourceFile, e.line, e.charPositionInLine, msg, true);
    problems.addProblem(problem);
  }

  public Problems getProblems() {
    return problems;
  }


}
