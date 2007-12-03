package mobius.prover.gui.editor.outline.types;

import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.swt.graphics.Image;


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
