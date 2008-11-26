package freeboogie.vcgen;

import freeboogie.ast.*;
import freeboogie.backend.Prover;

public class AxiomSender extends Transformer {
  private Prover prover;

  public void setProver(Prover prover) {
    this.prover = prover;
  }

  public void process(Declaration ast) {
    // TODO implement
  }
}
