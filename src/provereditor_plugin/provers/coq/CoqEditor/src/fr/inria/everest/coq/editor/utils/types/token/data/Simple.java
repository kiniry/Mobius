package fr.inria.everest.coq.editor.utils.types.token.data;

import fr.inria.everest.coq.editor.utils.types.Declaration;
import prover.gui.editor.ProverEditor;
import prover.gui.editor.outline.types.ProverType;


public class Simple extends ATokenData{

	public ProverType parse(ProverEditor editor) {
		return new Declaration(editor, fText, fOffset, fLen);
	}
	public Object clone() {
		return new Simple();
	}
}
