package fr.inria.everest.coq.editor.utils.types.token.data;

import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.outline.types.ProverType;
import fr.inria.everest.coq.editor.utils.types.Module;

public class ComplexBegin extends ATokenData{

	public ProverType parse(ProverEditor editor) {	
		Module m = new Module(editor, fText, fOffset);
		return m;
	}
	public Object clone() {
		return new ComplexBegin();
	}
}
