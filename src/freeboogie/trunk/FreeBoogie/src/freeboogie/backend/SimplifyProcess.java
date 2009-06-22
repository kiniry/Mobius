package freeboogie.backend;

import java.io.*;
import java.util.*;

/**
 *  Starts a Simplify/Z3 subprocess and manages sending string
 *  commands and parsing the prover responses. The goal is to
 *  have parsing that is robust enough to handle both Simplify
 *  and Z3 running in Simplify mode ("-si"). Also, the parsing
 *  should handle unexpected output gracefully.
 *
 *  NOTE: This class was first developed for ESC/Java
 *
 *  @author rgrig
 */
@SuppressWarnings("serial")
public class SimplifyProcess {
  private Process simplify; // the child process
  private BufferedReader in; // this is how we read what the prover says
  private PrintStream out; // this is how we tell stuff to the prover

  private boolean alive; // is the prover alive?
  private ArrayList<String[]> labels;

  /**
   * The typical values for {@code cmd} are {@code ["simplify"]}
   * and {@code ["z3","/si"]}. This starts a process and the
   * arguments select the command line to use to start the prover.
   *
   * @throws ProverException if creating the process fails
   */
  public SimplifyProcess(String[] cmd) throws ProverException {
    try {
      ProcessBuilder pb = new ProcessBuilder(cmd);
      simplify = pb.start();
      in = new BufferedReader(new InputStreamReader(simplify.getInputStream()));
      out = new PrintStream(simplify.getOutputStream(), true);
    } catch (Exception e) {
      if (simplify != null) stopProver();
      throw new ProverException("I can't run the prover.", e);
    }
    alive = true;
    labels = new ArrayList<String[]>();
  }

  /**
   *  Sends a command to the prover that is expected to not
   *  produce any (important) response from the prover.
   *  @throws ProverException if the provers seems to have died
   *    or something else goes terribly wrong
   */
  public void sendCommand(String cmd) throws ProverException {
    checkAlive();
//System.out.println(cmd);
    out.println(cmd);
    checkOut();
  }

  /**
   *  Sends a query to the prover. In case the prover response
   *  is "Invalid" (and hence we return false) the labels can
   *  be obtained by a subsequent call to {@code getLabels}.
   */
  public boolean isValid(String q) throws ProverException {
    checkAlive();
//System.out.println(q);
    out.println(q);
    checkOut();
    labels.clear();
    return parseResponse();
  }

  /**
   * Kills the child. (Or does nothing if he's already dead.)
   */
  public void stopProver() {
    alive = false;
    out.close(); // TODO: safe to close twice?
    try {
      simplify.waitFor();
    } catch (InterruptedException e) {
      // TODO: what should I do here?
    }
  }

  /**
   *  Returns the labels given by the last prover response.
   *  (An empty array is returned if the last query was valid.)
   */
  public String[][] getLabels() {
    return labels.toArray(new String[0][]);
  }

  private void checkAlive() throws ProverException {
    if (!alive) 
      throw new ProverException("Internal error: I shouldn't talk to a dead prover.");
  }

  private void checkOut() throws ProverException {
    if (out.checkError()) {
      alive = false;
      throw new ProverException("The prover seems to have died.");
    }
  }

  // TODO Explain the meaning
  private static enum ParseState {
    INSIDE,
    OUTSIDE,
    MATCH
  };

  private static final String INVALID_S = "invalid";
  private static final String VALID_S = "valid";
  private static final String LABELS_S = "labels";
  private static final String BAD_S = "bad input";

  /** Signals that something went really wrong while parsing. */
  private static class ParseError extends Exception {
    public ParseError(String m) {
      super(m);
    }
  }

  private char lastChar;
  private boolean peeked;

  private char peekChar() throws ParseError {
    if (peeked) return lastChar;
    lastChar = readChar();
    peeked = true;
    return lastChar;
  }

  private char simpleReadChar() throws ParseError {
    int c;
    try {
      c = in.read();
    } catch (IOException e) {
      throw new ParseError("Error reading from the prover.");
    }
    if (c == -1)
      throw new ParseError("Unexpected end of prover output. He probably died.");
    //System.out.print((char)c);
    return (char) c;
  }

  private char readChar() throws ParseError {
    if (peeked) {
      peeked = false;
      return lastChar;
    }
    char ch;
    int parenCnt = 0;
    do {
      ch = simpleReadChar();
      if (ch == '(') ++parenCnt;
      if (ch == ')') --parenCnt;
    } while (parenCnt > 0 || ch == ')');
    return ch;
  }

  // NOTE: this assumes at least one char between "labels" and "("
  private void parseLabels() throws ParseError {
    char c;
    ArrayList<String> counterexample = new ArrayList<String>();
    while (simpleReadChar() != '(');

    StringBuilder sb = new StringBuilder();
    ParseState ps = ParseState.OUTSIDE;
loop:
    while (true) {
      switch (ps) {
      case OUTSIDE:
        while (Character.isWhitespace(c = simpleReadChar())||c=='|');
        if (c == ')') break loop;
        sb.append(c);
        ps = ParseState.INSIDE;
        break;
      case INSIDE:
        while (!Character.isWhitespace(c = simpleReadChar())&&c!=')'&&c!='|')
          sb.append(c);
        counterexample.add(sb.toString());
        if (c == ')') break loop;
        sb.setLength(0);
        ps = ParseState.OUTSIDE;
        break;
      default:
        assert false : "Huh?";
      }
    }
    labels.add(counterexample.toArray(new String[0]));
  }

  private boolean result(int r) throws ProverException {
    switch (r) {
    case 0: return false;
    case 1: return true;
    default: 
      throw new ProverException("We sent something ugly to the prover.");
    }
  }

  /**
   *  Wait for "Invalid"/"Valid"/"Bad input" followed by a dot 
   *  outside parantheses. Also, capture labels that are signaled 
   *  by "labels" followed by "(...)".
   *
   *  TODO: This hangs for any other input. There should be
   *        some mechanism to recover from such a situation.
   */
  private boolean parseResponse() throws ProverException {
    char c = ' ', cl; // last read character, and its lowercase version
    ParseState ps = ParseState.OUTSIDE;
    String tomatch = null; // the word we try to match
    int matched = 0;
    int result = 0; // invalid/valid/fail
    boolean resultSeen = false;

    int i;
    try {
      while (true) {
        c = readChar();
        if (c == '.' && resultSeen) return result(result);
        switch (ps) {
        case OUTSIDE:
          if (Character.isLetter(c)) {
            cl = Character.toLowerCase(c);
            if (cl == 'i') {
              result = 0;
              tomatch = INVALID_S;
              matched = 1;
              ps = ParseState.MATCH;
            } else if (cl == 'v') {
              result = 1;
              tomatch = VALID_S;
              matched = 1;
              ps = ParseState.MATCH;
            } else if (cl == 'b') {
              result = 2;
              tomatch = BAD_S;
              matched = 1;
              ps = ParseState.MATCH;
            } else if (cl == 'l') {
              tomatch = LABELS_S;
              matched = 1;
              ps = ParseState.MATCH;
            } else ps = ParseState.INSIDE;
          }
          break;
        case INSIDE:
          if (!Character.isLetterOrDigit(c)) ps = ParseState.OUTSIDE;
          break;
        case MATCH:
          if (matched < tomatch.length()) {
            if (Character.toLowerCase(c) != tomatch.charAt(matched)) {
              ps = Character.isLetterOrDigit(c) ? 
                ParseState.INSIDE : ParseState.OUTSIDE;
            }
            ++matched;
          } else {
            if (!Character.isLetterOrDigit(c)) {
              if (tomatch == LABELS_S) parseLabels();
              else {
                resultSeen = true;
                if (c == '.') return result(result);;
              }
              ps = ParseState.OUTSIDE;
            } else ps = ParseState.INSIDE;
          }
          break;
        default:
          assert false: "Huh?";
        }
      }
    } catch (ParseError e) {
      stopProver();
      throw new ProverException("The prover is mumbling. I can't understand.");
    }
  }
}

