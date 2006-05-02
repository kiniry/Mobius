package fr.inria.everest.coq.editor.utils.types;


import org.eclipse.swt.graphics.Image;

import prover.gui.editor.ProverEditor;
import prover.gui.editor.outline.types.ProverType;

public class CoqType extends ProverType {
	String fName;
	protected Image fImg;

	
	public CoqType(ProverEditor editor, String name) {
		super(editor);
		fName = name;
	}
	
	public String toString() {
		return fName;
	}
	

	public void setEnd(int end) {
		setLength(end - getOffset());
	}

	public Image getImage() {
		return fImg;	
	}
}

