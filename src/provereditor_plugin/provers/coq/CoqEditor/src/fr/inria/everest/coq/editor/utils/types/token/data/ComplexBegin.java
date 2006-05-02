package fr.inria.everest.coq.editor.utils.types.token.data;

import fr.inria.everest.coq.editor.utils.types.Module;
import prover.gui.editor.ProverEditor;
import prover.gui.editor.outline.types.ProverType;

public class ComplexBegin extends ATokenData{

	public ProverType parse(ProverEditor editor) {	
		Module m = new Module(editor, fText, fOffset);
		return m;
	}
	public Object clone() {
		return new ComplexBegin();
	}
}
