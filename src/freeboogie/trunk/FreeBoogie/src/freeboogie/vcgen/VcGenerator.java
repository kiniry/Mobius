package freeboogie.vcgen;

import freeboogie.ast.*;
import freeboogie.backend.Term;

/**
 * A facade for the {@code freeboogie.vcgen} package.
 *
 * The user can ask for the verification condition (VC)
 * of an implementation by saying {@code vc(implementation)}.
 * A <i>threshold</i> is an indication for the maximal acceptable
 * size of a VC, measured in (dag) {@code Term} nodes. If
 * necessary, some assertions are ignored to obey the limit.
 */
public class VcGenerator {
  /* IMPLEMENTATION
   *
   * The phases of VC generation are:
   *  (1) make graphs reducible 
   *  (2) infer invariants 
   *  (3) cut loops 
   *  (4) desugar calls 
   *  (5) desugar havoc
   *  (6) desugar where clauses 
   *  (7) desugar specifications 
   *  (8) make passive 
   *  (9) strongest postcondition 
   * (10) add axioms, depending on the prover, for
   *      (a) the partial order <: 
   *      (b) map selection and updating
   *      (c) distinct constants (unique) 
   */

  public Term vc(Implementation implementation) {
    assert false; // TODO
    return null;
  }

  public void setThreshold(int size) {
    assert false; // TODO
  }
}
