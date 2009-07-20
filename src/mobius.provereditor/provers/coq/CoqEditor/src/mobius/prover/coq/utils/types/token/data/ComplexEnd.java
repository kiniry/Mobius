package mobius.prover.coq.utils.types.token.data;

import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.outline.types.ProverType;

public class ComplexEnd extends ATokenData {
  /** {@inheritDoc} */
  @Override
  public ProverType parse(final ProverEditor editor) {
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public Object clone() {
    return new ComplexEnd();
  }
}
