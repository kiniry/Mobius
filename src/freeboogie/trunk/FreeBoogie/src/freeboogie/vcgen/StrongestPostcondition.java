package freeboogie.vcgen;

import java.util.logging.Logger;

import freeboogie.ast.*;
import freeboogie.backend.Prover;
import freeboogie.backend.Term;
import freeboogie.backend.TermBuilder;
import freeboogie.backend.TermOfExpr;
import freeboogie.tc.*;

/**
 * Computes strongest postcondition for one {@code
 * Implementation}.
 *
 * The input AST must be acyclic and passive, meaning that
 * the only commands it is allowed to contain are of the type
 * {@code AssertAssumeCmd}. The procedures associated with
 * implementations are ignored: We assume that the contracts were
 * already desugared in properly placed assumes and asserts.
 *
 * The formula is built using a {@code TermBuilder} that
 * is handed to us by the user. That {@code TermBuilder}
 * must know about the terms "true", "and", "or", and "implies". The
 * expressions that appear inside {@code AssertAssumeCmd}s will
 * be transformed into formulas using the {@code TermOfExpr} that
 * is handed to us by the user. Typically the user would give
 * us a pair ({@code TermBuilder}, {@code TermOfExpr}) that are
 * provided by one {@code Prover}.
 *
 * @author rgrig
 * @author reviewed by TODO
 */
public class StrongestPostcondition {

  // used mainly for debugging
  static private final Logger log = Logger.getLogger("freeboogie.vcgen");

  // used to get flow graphs
  private TypeChecker typeChecker;

  // the flow graph of the implementation being processed
  private SimpleGraph<Block> flow;

  /**
   * Returns the postcondition for {@code impl}.
   */
  public Term getVc(Implementation impl) {
    Block entry = impl.getBody().getBlocks();
    assert false;
    // TODO Continue here
    return null;
  }

}
