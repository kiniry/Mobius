// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.Synex.Parser;

import Parser.Synex.Parser.Outcome;
import Parser.Synex.Parser.ParseFailure;
import Parser.Synex.Parser.ParseSuccess;
import Parser.Synex.Scanner.Scanner;
import Parser.Synex.Scanner.ScanFailureException;
import Parser.Synex.Grammar.Grammar;
import Parser.Synex.Grammar.ProductionInfo;
import Parser.Synex.Grammar.Args;
import Parser.Synex.Grammar.NonTerminal;
import Parser.Synex.Grammar.BadGrammarException;
import Parser.Synex.SynexException;

import java.io.DataInputStream;

public class Parser {

  public Outcome[] stack;
  public int stackTop;
  ProductionInfo noInfo;
  
  public Scanner scanner;

  public Parser(Scanner scanner) {
    this.scanner = scanner;
    this.stack = new Outcome[1000];
    this.stackTop = -1;
    this.stack[0] = null; // first info slot
    this.noInfo = new ProductionInfo("<none>", 0, 0);
  }
  
  public void reset() {
    scanner.reset();
    // The stack is self-clearing because of try-finally statements 
  }
  
  public void readFrom(String streamName, DataInputStream rd) {
    scanner.pushInput(streamName, rd, true);
  }

  public String syntaxErrorMsg(ParseFailure failure) {
    return scanner.syntaxMsg(failure.msg);
  }
  
  public Outcome parse(NonTerminal nonTerminal) {
  /** To parse a non-terminal. Parsing (and user-action) exceptions are turned 
      into ParseFailure outcomes. */
    try {
      return nonTerminal.accept(this);
    } catch (SynexException ex) {
          return new ParseFailure(scanner.getLocation(), ex.getMessage());
    }
  }
  
  public Outcome fetch(int n) throws BadGrammarException {
  /** To fetch the n-th item off the current parser stack frame. N.B., could return null. */
    if ((n < 0) || (n >= currentInfo().frameSize)) {
      throw new BadGrammarException(
        "Index out of range in production '" + currentInfo().productionName 
        + "', fetching: " + Integer.toString(n));
    }
    return stack[stackTop-n];
  }

/** Internal use */

  public void pushStack(ProductionInfo info, Args args) throws BadGrammarException {
    /** The corresponding popStack call should be placed in a try-finally to make 
        sure the stack is cleaned-up. */
    int frameSize = info.frameSize;
    while (stackTop+frameSize+2 >= stack.length) {
      Outcome[] buf = new Outcome[2*stack.length];
      for (int i = 0; i < stack.length; i++) { buf[i] = stack[i]; }
      stack = buf;
    }
    int previousStackTop = stackTop;
    stackTop += frameSize + 1; // skip current info slot
    stack[stackTop+1] = info; // info out of the way above frame
    if ((info.argsNo > 0) || (args != null)) { // parameter passing
      Args actuals = args;
      int formals = info.argsNo;
      int argNo = 0;
      while ((formals > 0) && (actuals != null)) {
        stack[stackTop-argNo] = stack[previousStackTop-actuals.argDispl];
        actuals = actuals.next;
        formals--;
        argNo++;
      }
      if ((formals > 0) || (actuals != null)) {
        while (actuals != null) { actuals = actuals.next; argNo++; }
        throw new BadGrammarException(
          "Wrong number of arguments to parameterized production '" + info.productionName 
          + "': " + Integer.toString(argNo) + " instead of " + Integer.toString(info.argsNo));
      }
    }
  }
  
  public void popStack() {
    int frameSize = currentInfo().frameSize;
    for (int i = stackTop+1; i > stackTop-frameSize;  i--) { stack[i] = null; }
    stackTop -= frameSize+1;
  }
  
  public ProductionInfo currentInfo() {
    /* returns null if stack is empty */
    Outcome outcome = stack[stackTop+1];
    if (outcome == null) { return noInfo; }
    return (ProductionInfo)outcome;
  }
  
}
