/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser;

import ie.ucd.bon.Main;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.Context;
import ie.ucd.bon.typechecker.FormalTypeChecker;
import ie.ucd.bon.typechecker.informal.InformalTypeChecker;
import ie.ucd.bon.util.NullOutputStream;

import java.io.File;
import java.io.PrintStream;

import org.antlr.runtime.BitSet;
import org.antlr.runtime.IntStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;
import org.antlr.runtime.Token;
import org.antlr.runtime.tree.TreeNodeStream;
import org.antlr.runtime.tree.TreeParser;

public class AbstractBONTCWalker extends TreeParser {

  private File sourceFile;
  private final Context context;
  private InformalTypeChecker itc;
  private FormalTypeChecker ftc;
  
  public AbstractBONTCWalker(TreeNodeStream input, RecognizerSharedState state) {
    super(input, state);
    this.context = Context.getContext();
  }
  
  public void initialise(TreeNodeStream input, InformalTypeChecker itc, FormalTypeChecker ftc, File sourceFile) {
    this.reset();
    this.setTreeNodeStream(input);
    this.itc = itc;
    this.ftc = ftc;
    this.sourceFile = sourceFile;
    this.context.reset();
  }

  public InformalTypeChecker getITC() {
    return itc;
  }
  
  public FormalTypeChecker getFTC() {
    return ftc;
  }
  
  public Context getContext() {
    return context;
  }

  public final SourceLocation getSourceLocation(Token t) {
    return new SourceLocation(t, sourceFile);
  }
  
  public final SourceLocation getSourceLocation(Token t1, Token t2) {
    return new SourceLocation(t1, t2, sourceFile);
  }
  
  //Just a shorter version
  public final SourceLocation getSLoc(Token t) {
    return getSourceLocation(t);
  }
  
  //Just a shorter version
  public final SourceLocation getSLoc(Token t1, Token t2) {
    return getSourceLocation(t1, t2);
  }
  
  public void displayRecognitionError(String[] tokenNames, RecognitionException e) {
    if (Main.isDebug()) {
      super.displayRecognitionError(tokenNames, e);
    }
  }
  
  public void emitErrorMessage(String msg) {
    System.out.println(msg);
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
  
}
