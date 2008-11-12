package freeboogie.backend;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Deque;
import java.util.List;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

import freeboogie.util.Err;

/**
 * Used to interact with Simplify and Z3 (when run in Simplify
 * interactive <tt>/si</tt> mode). 
 *
 * The responsibilities of this class are:
 *  (1) Prepare the {@code TermBuilder} by registering the
 *      appropriate symbols recognized by Simplify;
 *  (2) Unfold shared {@code SmtTerm}s by introducing temporary
 *      variables; (NOTE: the definitions should use FLET for Z3
 *      and IFF for simplify; TODO perhaps have two classes?)
 *  (3) Transform {@code SmtTerm} objects into the string
 *      representation;
 *  (4) TODO Take care of array axiomatization. Later on we should
 *      change this to take advantage of the built in arrays in Z3.
 *
 * @author rgrig 
 */
public class SimplifyProver extends Prover {
  /* IMPLEMENTATION NOTE:
   * The reason why strings are built, instead of sending pieces
   * to the output stream is that it is easier to debug. The downside
   * is that we use O(n) memory instead of O(1) just for printing,
   * where n is the size of the formula.
   */
  private SimplifyProcess simplify;
  private StringBuilder strBuilder;
  
  /**
   * Creates new {@code SimplifyProver}. It also tries to start the prover.
   *
   * @param cmd the command to use to start the prover
   * @throws ProverException if the prover cannot be started
   */
  public SimplifyProver(String[] cmd) throws ProverException {
    simplify = new SimplifyProcess(cmd);
    strBuilder = new StringBuilder();
    prepareTermBuilder();
  }

  /**
   * Prepares an {@code SmtTermBuilder} that knows about the
   * sorts and operators that Simplify understands.
   */
  private void prepareTermBuilder() {
    builder = new SmtTermBuilder();
  }

  // TODO This is quite incomplete now
  // TODO Exploit the regularity to make the code nicer
  private void printTerm(Term t, StringBuilder sb) {
    SmtTerm st = (SmtTerm)t;
    if (st.id.startsWith("var")) { 
      sb.append((String)st.data);
    } else if (st.id.startsWith("forall")) {
      sb.append("(FORALL (");
      printTerm(st.children[0], sb);
      sb.append(") ");
      printTerm(st.children[1], sb);
      sb.append(")");
    } else if (st.id.equals("literal_int")) {
      sb.append(st.data);
    } else if (st.id.equals("literal_bool")) {
      if ((Boolean)st.data)
        sb.append("TRUE");
      else
        sb.append("FALSE");
    } else if (st.id.startsWith("map_update")) {
      sb.append("($$update ");
      printArgs(st.children, sb);
      sb.append(")");
    } else if (st.id.startsWith("map_select")) {
      sb.append("($$select ");
      printArgs(st.children, sb);
      sb.append(")");
    } else if (st.id.equals("tuple")) {
      printArgs(st.children, sb);
    } else if (st.id.startsWith("xor")) {
      sb.append("(NOT (IFF ");
      printTerm(st.children[0], sb);
      sb.append(" ");
      printTerm(st.children[1], sb);
      sb.append("))");
    } else if (st.id.startsWith("eq")) {
      sb.append("(EQ ");
      printTerm(st.children[0], sb);
      sb.append(" ");
      printTerm(st.children[1], sb);
      sb.append(")");
    } else {
      sb.append("(");
      sb.append(st.id.toUpperCase());
      for (Term c : st.children) {
        sb.append(" ");
        printTerm(c, sb);
      }
      sb.append(")");
    }
  }

  private void printArgs(Term[] a, StringBuilder sb) {
    for (int i = 0; i < a.length; ++i) {
      if (i != 0) sb.append(" ");
      printTerm(a[i], sb);
    }
  }

  @Override
  protected void sendAssume(Term t) throws ProverException {
    strBuilder.setLength(0);
    strBuilder.append("(BG_PUSH ");
    printTerm(t, strBuilder);
    strBuilder.append(")");
    simplify.sendCommand(strBuilder.toString());
    log.fine("simplify BG_PUSH: " + strBuilder);
  }

  @Override
  protected void sendRetract() throws ProverException {
    simplify.sendCommand("(BG_POP)");
    log.fine("simplify BG_POP");
  }
  
  @Override
  public boolean isValid(Term t) throws ProverException {
    strBuilder.setLength(0);
    printTerm(t, strBuilder);
    log.fine("ask simplify: " + strBuilder);
    boolean r = simplify.isValid(strBuilder.toString());
    log.fine("simplify says: " + r);
    return r;
  }

  @Override
  public String[][] getLabels() {
    return simplify.getLabels();
  }

  @Override
  public void terminate() {
    simplify.stopProver();
    log.info("I tried to kill the prover. Hope it's dead.");
  }
  
  /**
   * Runs some basic tests.
   * @param args the command line arguments
   * @throws Exception thrown if something goes wrong
   */
  public static void main(String[] args) throws Exception {
    try {
      FileHandler logh = new FileHandler("simplify.log");
      logh.setFormatter(new SimpleFormatter());
      log.addHandler(logh);
      log.setUseParentHandlers(false);
      //log.setLevel(Level.WARNING); // for release
      log.setLevel(Level.ALL); // for debug
    } catch (IOException e) {
      Err.warning("Can't create log file. Nevermind.");
      log.setLevel(Level.OFF);
    }
    
    Prover p = new SimplifyProver(args);
    TermBuilder b = p.getBuilder();
    Term x = b.mk("var_pred", "x");
    Term y = b.mk("var_pred", "y");
    Term q = b.mk("not", b.mk("iff", 
      b.mk("iff", b.mk("and", x, y), b.mk("or", x, y)),
      b.mk("iff", x, y)
    ));
    System.out.println("false = " + p.isValid(q));
  }
}
