package freeboogie.vcgen;

import freeboogie.backend.Prover;
import freeboogie.backend.TermBuilder;
import freeboogie.backend.TermOfExpr;

/**
 * Computes strongest postcondition for one {@code
 * Implementation}.
 *
 * The input AST must be acyclic and passive, meaning that
 * the only commands it is allowed to contain are of the type
 * {@code AssertAssumeCmd}. The procedures associated with
 * implementations are ignore: We assume that the contracts were
 * already desugared in properly placed assumes and asserts.
 *
 * The formula is built using a {@code TermBuilder} that is
 * handed to us by the user. That {@code TermBuilder} must
 * know about the terms "and", "or", "implies", and "not". The
 * expressions that appear inside {@code AssertAssumeCmd}s will
 * be transformed intu formulas using the {@code TermOfExpr} that
 * is handed to us by the user. Typically the user would give
 * us a pair ({@code TermBuilder}, {@code TermOfExpr}) that are
 * provided by one {@code Prover}.
 *
 * @author rgrig
 * @author reviewed by TODO
 */
public class StrongestPostcondition {
}
