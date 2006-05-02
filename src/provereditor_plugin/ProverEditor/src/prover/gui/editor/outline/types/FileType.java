package prover.gui.editor.outline.types;

import org.eclipse.swt.graphics.Image;

import prover.gui.editor.ProverEditor;

public class FileType extends ProverType {
	String fName;
	Image fImg;
	public FileType(ProverEditor editor, String name, Image image) {
		super(editor);
		fName = name;
		fImg = image;
	}
	
	public String toString() {
		return fName;
	}
	public Image getImage() {
		return fImg;
	}
}
