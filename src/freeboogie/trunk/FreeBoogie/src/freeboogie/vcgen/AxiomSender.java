package freeboogie.vcgen;

import java.util.HashSet;
import java.util.Set;

import freeboogie.ast.*;
import freeboogie.backend.*;

/**
 * Sends Boogie axioms to the prover.
 */
public class AxiomSender<T extends Term<T>> extends Transformer {
  private Prover<T> prover;
  private TermBuilder<T> term;
  private Set<T> axioms = new HashSet<T>(109);

  public void setProver(Prover<T> prover) {
    this.prover = prover;
    this.term = prover.getBuilder();
  }

  public void process(Declaration ast) throws ProverException {
    axioms.clear();
    ast.eval(this);
    for (T t : axioms) prover.assume(t);
  }

  @Override
  public void see(Axiom axiom, Identifiers typeVars, Expr expr, Declaration tail) {
    T a = term.of(expr);
    axioms.add(a);
    a.collectAxioms(axioms);
    if (tail != null) tail.eval(this);
  }
}
