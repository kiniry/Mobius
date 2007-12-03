package fr.inria.everest.coq.editor.utils.types.token.data;

import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.outline.types.ProverType;
import fr.inria.everest.coq.editor.utils.types.Declaration;


public class Simple extends ATokenData{

	public ProverType parse(ProverEditor editor) {
		return new Declaration(editor, fText, fOffset, fLen);
	}
	public Object clone() {
		return new Simple();
	}
}
