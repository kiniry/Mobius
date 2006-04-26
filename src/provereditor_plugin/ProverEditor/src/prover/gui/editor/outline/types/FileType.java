package prover.gui.editor.outline.types;

import org.eclipse.swt.graphics.Image;

public class FileType extends ProverType {
	String fName;
	Image fImg;
	public FileType(String name, Image image) {
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
