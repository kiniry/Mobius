package prover.gui.editor.outline;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import prover.gui.editor.outline.types.ProverType;

public class TypeContentProvider implements ITreeContentProvider {
	private static final Object[] EMPTY_ARRAY = new Object[0];

	public void dispose() {
		// TODO Auto-generated method stub

	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		// TODO Auto-generated method stub
	}

	public Object[] getChildren(Object parent) {
		if(parent instanceof ProverType) {
			return ((ProverType)parent).getSubtypes();
		}
		return EMPTY_ARRAY;
	}

	public Object getParent(Object elem) {
		if(elem instanceof ProverType) {
			return ((ProverType)elem).getSupertype();
		}
		return null;
	}

	public boolean hasChildren(Object elem) {
		if(elem instanceof ProverType) {
			Object[] os = ((ProverType)elem).getSubtypes();
			return (os != null) && (os.length > 0);
		}
		return false;
	}

	public Object[] getElements(Object input) {
		return getChildren(input);
	}

}
