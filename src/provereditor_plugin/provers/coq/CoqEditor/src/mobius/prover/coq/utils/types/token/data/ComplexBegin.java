package mobius.prover.coq.utils.types.token.data;

import mobius.prover.coq.utils.types.Module;
import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.outline.types.ProverType;

public class ComplexBegin extends ATokenData {
  /** {@inheritDoc} */
  @Override
  public ProverType parse(final ProverEditor editor) {  
    final Module m = new Module(editor, fText, fOffset);
    return m;
  }
  
  /** {@inheritDoc} */
  @Override
  public Object clone() {
    return new ComplexBegin();
  }
}
