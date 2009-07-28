// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

/** A scanner skeleton superclass. To be subclassed by user-defined actual scanners. 
    Input sources for scanning must be added by pushInput(). 
    The client subclass must override nextToken(); the code for nextToken should 
    obtain characters by calling the provided lookChar(), getChar(), and haveChar().
    The client subclass may need to extend clear() to reset the scanner on errors 
    (by overriding it and still calling super.clear()) */

package Parser.Synex.Scanner;

import java.io.IOException;
import java.io.DataInputStream;

import Parser.Synex.Scanner.ScanFailureException;
import Parser.Synex.Scanner.ScannerInput;
import Parser.Synex.Scanner.Token;
import Parser.Synex.Scanner.Location;

public abstract class Scanner {
/** === A scanner */

/** === PRIVATE FIELDS === */

  private ScannerInput currentInput;
  private ScannerInput lastReadInput;
  private Location noLocation;
  private Location lastLocation;
  
  boolean lookAheadReady;
  char lookAheadChar;
  boolean tokenReady;
  Token currentToken;
  int scanPoint;

/** === PUBLIC METHODS === */

/** === Constructors === */

  public Scanner() {
  /** Constructor. 
       A brand new scanner.
       The input stack is empty; must use pushInput() to initialize.
       Use it single-threaded. You can use separate scanners with separate threads, 
       concurrently. */
    scanPoint = 0;
    lookAheadReady = false;
    tokenReady = false;
    currentInput = null;
    lastReadInput = null;
    noLocation = new Location("<no stream>", 0, 0, 0);
    lastLocation = noLocation;
  }
  
/** === Tokenizer === */

  public abstract Token nextToken() throws ScanFailureException;
  /* Must be defined in subclasses.
     Should rise ScanFailureException if it cannot return a token. */
  
  private Token lookToken() throws ScanFailureException {
    if (!tokenReady) {
      ScannerInput input = currentInput; // currentInput may become null after nextToken()
      int tokenBegPos = (input == null) ? 0 : input.charPos;
      currentToken = nextToken();
      currentToken.tokenBegPos = tokenBegPos;
      currentToken.tokenEndPos = (input == null) ? tokenBegPos : input.charPos;
      tokenReady = true;
    }
    return currentToken;
  }
  
  public Token getToken() throws ScanFailureException {
    if (!tokenReady) { currentToken = lookToken(); }
    tokenReady = false;
    scanPoint++;
    return currentToken;
  }

  public boolean haveToken(Token token) throws ScanFailureException {
    if (lookToken().equal(token)) {
      currentToken = getToken();
      return true;
    } else {
      return false;
    }
  }

  public Token matchToken(Token token) throws ScanFailureException {
    if (lookToken().match(token)) {
      return getToken();
    } else {
      return null;
    }
  }

/** === Character reader support for the client's nextToken() === */

  public static char EofChar = '\377';
  
  public char lookChar() throws ScanFailureException {
  /** Peek at the next character without accepting it. */
    char ch;
    if (lookAheadReady) { return lookAheadChar; }
    if (currentInput == null) { throw new ScanFailureException("Unexpected end of stream"); }
    try {
      lastReadInput = currentInput;
      ch = currentInput.readChar();
      lookAheadChar = ch;
      lookAheadReady = true;
    }
    catch (IOException ex) {
      if (currentInput.generateEOF) {
        lookAheadChar = EofChar;
        lookAheadReady = true;
        ch = EofChar;
        popInput();
      } else {
        popInput();
        ch = lookChar();
      }
    }
    return ch;
  }

  public char getChar() throws ScanFailureException {
  /** Accept the next character. */
    if (!lookAheadReady) { lookChar();}
    lastReadInput.advance(lookAheadChar);
    lookAheadReady = false;
    return lookAheadChar;
  }
  
  public boolean haveChar(char ch) throws ScanFailureException {
  /** Test to see if the next character is ch, and in that case accept it. */
    if (ch == lookChar()) {
      char c = getChar();
      return true;
    } else {
      return false;
    }
  }
  
/** === Input Source Handling === */

  public void pushInput(String streamName, DataInputStream rd, 
      boolean closeReader) {
  /** Switch the scanner input to a new reader, and push the existing
       one on the input stack. Scanning from the old reader will resume from 
       the current position when the new one is exhausted. If closeReader
       is true, the reader is closed when rd is exhausted. If genereteEOF
       is true, an Eof token is generated when rd is exhausted. */
    pushInput(streamName, rd, closeReader, true);
  }

  public void pushInput(String streamName, DataInputStream rd, 
      boolean closeReader, boolean generateEOF) {
    currentInput = new ScannerInput(streamName, rd, currentInput, closeReader, generateEOF);
  }

  public void popInput() throws ScanFailureException {
  /** Discards the current reader and switches back to the previous 
       reader in the input stack. Raises ScanFailureException if there is no
       previous reader. Closes the current reader, if it was so requested
       at PushInput time. An Eof token is not generated, even if it was
       so requested at PushInput time. */
    if (currentInput == null) { throw new ScanFailureException("Unexpected end of stream"); }
    try { if (currentInput.closeReader) { currentInput.close(); } }
    catch (IOException ex) {}
    currentInput = currentInput.next;
  }
  
  public int getScanPoint() {
  /** The number of tokens read so far. Useful in LL(1) parsers to detect
       illegal backtracking. */
    return scanPoint;
  }
  
  private Location getLocationFrom(ScannerInput input) {
    if ((input.streamName != lastLocation.streamName) ||
        (input.charPos != lastLocation.chr)) {
      lastLocation = 
        new Location(input.streamName, input.charPos, input.linePos, input.lineCharPos);
    }
    return lastLocation;
  }
  
  public Location getLocation() {
  /** Get the streamName and position of the current input reader. */
    if ((lastReadInput == null) && (currentInput == null)) {
      return noLocation;
    } else if (lastReadInput != null) {
      return getLocationFrom(lastReadInput);
    } else {
      return getLocationFrom(currentInput);
    }
  }
  
  public void clear() {
  /** Clean up the scanner state, but preserve the input file stack. 
       Buffered characters and tokens are discarded. */
    try {
      if (lookAheadReady) {char ch = getChar();}
      if (tokenReady) {currentToken = getToken();}
    }
    catch (ScanFailureException ex) {}
  }
  
  public void reset() {
  /** Reinitialize the scanner state. It calls Clear and empties the file stack.
      Reset is useful for clearing the scanner after a scanning or parsing error. */
    clear();
    try { while (true) { popInput(); }
    } catch (ScanFailureException ex) { lastReadInput = null; }
  }
  
/** === Error messages === */
  
  public String syntaxMsg(String cause) {
    return syntaxMsg(cause, true);
  }
  
  public String syntaxMsg(String cause, boolean linePlusCharStyle) {
  /**  cause should specify the general reason of the error and 
       the specific offender, or be "". It prints error positions according to 
       linePlusCharStyle; either line+char or absolute char. */
    Location info = getLocation();
    String msg = "";
    if (cause.length() > 0) { msg += cause + " "; }
    if (linePlusCharStyle) { msg += info.streamLineCharMsg(); }
    else { msg += info.streamAbsoluteCharMsg(); }
    reset();
    return msg;
  }
  
}
