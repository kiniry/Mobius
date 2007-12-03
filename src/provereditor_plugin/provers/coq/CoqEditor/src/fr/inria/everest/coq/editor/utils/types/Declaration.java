package fr.inria.everest.coq.editor.utils.types;

import mobius.prover.gui.editor.ProverEditor;
import fr.inria.everest.coq.editor.CoqProverTranslator;

public class Declaration extends CoqType {

	public Declaration(ProverEditor editor, String name, int offset, int len) {
		super(editor, name.trim());
		setOffset(offset);
		setLength(len);
		name = name.trim();
		if(name.startsWith("Module")) {
			fImg = CoqProverTranslator.imgs[1];
			name = name.substring(0, name.length() - 2);
			fName = name;
			setLength(len - 2);
		}else if(name.startsWith("Declare Module")) {
			fImg = CoqProverTranslator.imgs[1];
		}
		else if(name.startsWith("Inductive")) {
			fImg = CoqProverTranslator.imgs[4];
			name = name.substring(0, name.length() - 2);
			fName = name;
			setLength(len - 2);
		}
		else if(name.startsWith("Parameter")) {
			fImg = CoqProverTranslator.imgs[5];
			name = name.substring(0, name.length() - 1);
			fName = name;
			setLength(len - 2);
		}
		else if(name.startsWith("Definition")) {
			int i = name.indexOf(":=");
			if(i == -1) {
				i = name.length() -1;
			}
			name = name.substring(0, i);
			fName = name;
			fImg = CoqProverTranslator.imgs[3];
		}
		else if(name.startsWith("Fixpoint")) {
			int i = name.indexOf(":=");
			if(i == -1) {
				i = name.length() -1;
			}
			name = name.substring(0, i);
			fName = name;
			fImg = CoqProverTranslator.imgs[8];
		}
		else if(name.startsWith("Record")) {
			int i = name.indexOf(":=");
			if(i == -1) {
				i = name.length() -1;
			}
			name = name.substring(0, i);
			fName = name;
			fImg = CoqProverTranslator.imgs[9];
		}
		else if(name.startsWith("Let")) {
			int i = name.indexOf(":=");
			if(i == -1) {
				i = name.length() -1;
			}
			name = name.substring(0, i);
			fName = name;
			fImg = CoqProverTranslator.imgs[10];
		}
		else if(name.startsWith("Scheme")) {
			name = name.substring(0, name.length() -2);
			fName = name;
			fImg = CoqProverTranslator.imgs[6];
			setLength(len -2);
		}
		else {
			fImg = CoqProverTranslator.imgs[7];
		}
	}


}
