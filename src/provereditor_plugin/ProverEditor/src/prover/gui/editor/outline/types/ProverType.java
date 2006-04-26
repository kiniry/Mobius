package prover.gui.editor.outline.types;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.swt.graphics.Image;

public class ProverType {
	private List subtypes = new ArrayList();
	private ProverType supertype = null;
	
	
	
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
}
