package prover.gui.editor.outline.types;

import java.util.ArrayList;
import java.util.Iterator;
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
		pt.addPath(getPath());
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

	String fPath = toString();
	public String getPath() {
		return fPath;
	}
	private void addPath(String path) {
		fPath = path + "." + toString();
	}	
	public String toString() {
		return "root";
	}

	public ProverType findFromPath(String path) {
		if(!path.startsWith(fPath))
			return null;
		if(path.length() == fPath.length())
			return this;
		Iterator iter = subtypes.iterator();
		while(iter.hasNext()) {
			ProverType pt = (ProverType)iter.next();
			ProverType res = pt.findFromPath(path);
			if(res != null)
				return res;
		}
		return null;
	}
	
}
