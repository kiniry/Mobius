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
   *  (4) desugar specifications 
   *  (5) desugar calls 
   *  (6) desugar havoc and where clauses 
   *  (7) make passive 
   *  (8) strongest postcondition 
   *  (9) add axioms, depending on the prover, for
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
