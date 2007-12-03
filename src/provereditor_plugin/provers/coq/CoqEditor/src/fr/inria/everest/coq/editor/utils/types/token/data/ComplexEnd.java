package fr.inria.everest.coq.editor.utils.types.token.data;

import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.outline.types.ProverType;

public class ComplexEnd extends ATokenData{
  public ProverType parse(ProverEditor editor) {
    return null;
  }
  public Object clone() {
    return new ComplexEnd();
  }
}
