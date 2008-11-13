package freeboogie.vcgen;

import freeboogie.ast.Transformer;
import freeboogie.backend.Prover;

public class AxiomSender extends Transformer {
  private Prover prover;

  public void setProver(Prover prover) {
    this.prover = prover;
  }
}
