package fr.inria.everest.coq.editor.utils.types;

import prover.gui.editor.ProverEditor;
import fr.inria.everest.coq.editor.CoqProverTranslator;



public class Module extends CoqType{
	

	private String fShortName;

	public Module(ProverEditor editor, String name, int start) {
		super(editor, name.trim());	

		String [] tab = toString().split(" ");
		fShortName = tab[1];
		if(tab[1].equals("Type")) {
			fShortName = tab[2];
		}
		fImg = CoqProverTranslator.imgs[0];
		setOffset(start);
	}


	public String getShortName() {
		return fShortName;
	}

	public String toString() {
		return super.toString();
	}
	

	
}
