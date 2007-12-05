package fr.inria.everest.coq.editor.utils.types.token.data;

import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.outline.types.ProverType;
import fr.inria.everest.coq.editor.utils.types.Declaration;


public class Simple extends ATokenData {
  /** {@inheritDoc} */
  @Override
  public ProverType parse(final ProverEditor editor) {
    return new Declaration(editor, fText, fOffset, fLen);
  }  
  
  /** {@inheritDoc} */
  @Override
  public Object clone() {
    return new Simple();
  }
}
