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
    // TODO some of this stuff is probably common to multiple provers
    //      so move it into the builder
    builder = new SmtTermBuilder();
    builder.def("not", new Sort[]{Sort.PRED}, Sort.PRED);
    builder.def("and", Sort.PRED, Sort.PRED);
    builder.def("or", Sort.PRED, Sort.PRED);
    builder.def("implies", new Sort[]{Sort.PRED, Sort.PRED}, Sort.PRED);
    builder.def("iff", new Sort[]{Sort.PRED, Sort.PRED}, Sort.PRED);
    builder.def("var_int", String.class, Sort.VARINT);
    builder.def("var_bool", String.class, Sort.VARBOOL);
    builder.def("var_pred", String.class, Sort.PRED);
    builder.def("const_int", BigInteger.class, Sort.INT);
    builder.def("const_bool", Boolean.class, Sort.BOOL);
    builder.def("forall_int", new Sort[]{Sort.VARINT, Sort.PRED}, Sort.PRED);
    builder.def("<", new Sort[]{Sort.INT, Sort.INT}, Sort.PRED);
    builder.def("<=", new Sort[]{Sort.INT, Sort.INT}, Sort.PRED);
    builder.def(">", new Sort[]{Sort.INT, Sort.INT}, Sort.PRED);
    builder.def(">=", new Sort[]{Sort.INT, Sort.INT}, Sort.PRED);
    builder.def("eq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.PRED);
    builder.def("eq_bool", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.PRED);
    // TODO register all stuff with the builder
    // TODO should I leave the user (vcgen) responsible for adding the
    //      excluded middle for boolean variables? i think that's in the
    //      escjava background predicate anyway
    builder.pushDef(); // mark the end of the prover builtin definitions
    log.info("prepared term builder for simplify");
  }

  // TODO This is quite incomplete now
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
    } else if (st.id.equals("const_int")) {
      sb.append(st.data);
    } else if (st.id.equals("const_bool")) {
      if ((Boolean)st.data)
        sb.append("|true|");
      else
        sb.append("|false|");
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
