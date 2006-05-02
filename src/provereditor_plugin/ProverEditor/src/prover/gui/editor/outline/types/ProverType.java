package prover.gui.editor.outline.types;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.swt.graphics.Image;

import prover.gui.editor.ProverEditor;

public class ProverType {
	private List subtypes = new ArrayList();
	private ProverType supertype = null;
	
	private int fOffset = 0;
	private int fLength = 0;
	private ProverEditor fEditor;
	
	public ProverType(ProverEditor editor) {
		fEditor = editor;
	}
	
	public int getLength() {
		return fLength;
	}

	protected void setLength(int length) {
		fLength = length;
	}

	public int getOffset() {
		return fOffset;
	}

	protected void setOffset(int offset) {
		fOffset = offset;
	}

	public void add(ProverType pt) {
		subtypes.add(pt);
		pt.supertype = this;
	}

	public Object [] getSubtypes() {
		return subtypes.toArray();
	}
	public Object getSupertype() {
		return supertype;
	}
	public Image getImage() {
		return null;
	}

	public void selectAndReveal() {	
		//System.out.println(fOffset + " " + fLength);
		if(fOffset != 0 || fLength != 0) {
			
			fEditor.selectAndReveal(fOffset, fLength);
		}
	}

	
}
