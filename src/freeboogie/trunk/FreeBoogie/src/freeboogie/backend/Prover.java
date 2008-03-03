package freeboogie.backend;

import java.util.*;
import java.util.logging.*;

/**
 * A prover can be used to check if a formula is valid.
 *
 * The formula must be built using a {@code TermBuilder} obtained
 * by calling {@code getBuilder}, otherwise you are on your own.
 * The validity of a formula is checked using {@code isValid()}
 * and it is done in the context give by the assumption stack; A
 * detailed answer (such as counterexamples) can be obtained by a
 * subsequent call to {@code getDetailedAnswer}.
 *
 * As a convenience, provers might offer "assumption frames" thru
 * the methods {@code push()} and {@code pop()}. A call to {@code
 * pop()} should {@code retract()} all assumptions since the
 * corresponding {@code push()}.
 *
 * The user can forcibly {@code terminate()} the prover, thereby
 * releasing most resources (memory, file handles,...).
 *
 * In the event that the prover dies a {@code ProverException}
 * should be thrown and the prover restarted. The user code
 * should be able to assume that the prover is in the state it
 * was before the failing operation was attempted.
 * 
 * TODO add properties, like timelimit
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public abstract class Prover {
  protected Deque<Term> assumptions;
  protected static final Term marker = new Term(null);
    // marks the end of an assumption frame in |assumptions|

  protected TermBuilder builder;
  protected TermOfExpr termOfExpr;
  protected static final Logger log = Logger.getLogger("freeboogie.backend");

  public Prover() {
    assumptions = new ArrayDeque<Term>();
  }

  /**
   * Returns a term builder whose terms are understood by this prover.
   * @return a builder for terms and formulas
   */
  public TermBuilder getBuilder() {
    return builder;
  }

  /**
   * Returns an object that builds terms recognized by this prover
   * out of BoogiePL expressions ({@see freeboogie.ast.Expr}).
   */
  public TermOfExpr getTermOfExpr() {
    return termOfExpr;
  }
  
  /**
   * Adds {@code t} as an assumption. Should add successfully sent
   * assumptions to {@code assumptions}.
   *
   * @param t the assumption
   * @throws ProverException if something goes wrong
   */
  public void assume(Term t) throws ProverException {
    assert t != null;
    sendAssume(t);
    assumptions.addLast(t);
  }

  /**
   * Actually sends {@code t} to the prover as an assumption.
   */
  abstract protected void sendAssume(Term t) throws ProverException;
  
  /**
   * Retract the last assumption. This discards all the empty 
   * assumption frames created after the last assumption. Should
   * remove any successfully removed assumption from {@code assumptions}.
   *
   * @throws ProverException if something goes wrong
   */
  public void retract() throws ProverException {
    int i, j;
    while (!assumptions.isEmpty() && assumptions.peekFirst() == marker)
      assumptions.removeFirst();
    assert !assumptions.isEmpty();
    sendRetract();
    assumptions.removeFirst();
  }

  /**
   * Asks the prover to disregard the last assumption.
   */
  abstract protected void sendRetract() throws ProverException;
  
  /**
   * Make a new frame of assumptions.
   * @throws ProverException if something goes wrong
   */
  public void push() throws ProverException {
    assumptions.addFirst(marker);
  }
  
  /**
   * Removes the last frame of assumptions.
   * @throws ProverException if something goes wrong
   */
  public void pop() throws ProverException {
    Term t;
    do t = assumptions.removeFirst();
    while (t != marker);
  }

  /**
   * Checks whether {@code t} is valid, given the existing
   * assumptions.
   * 
   * @param t the query, must have sort PRED 
   * @return whether {@code t} is valid 
   * @throws ProverException if something goes wrong
   */
  abstract public boolean isValid(Term t) throws ProverException;
  
  /**
   * If the last call to {@code isValid} returned false then
   * return an array with counterexamples. Each counterexample
   * is an array of labels. The result is always nonnull, but
   * may be empty. The result is empty if the last call to
   * {code isValid} returned true.
   */
  abstract public String[][] getLabels();

  /**
   * Terminates the prover. This should release memory, free CPU,
   * and so on.
   */
  abstract public void terminate();
}
