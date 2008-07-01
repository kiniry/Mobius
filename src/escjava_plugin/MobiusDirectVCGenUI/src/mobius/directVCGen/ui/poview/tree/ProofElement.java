package mobius.directVCGen.ui.poview.tree;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.TreeViewer;

public abstract class ProofElement extends WorkspaceElement {
	public ProofElement(IResource key) {
		super(key);
	}

	public void compile(TreeViewer viewer) {
		WorkspaceElement [] tab = (WorkspaceElement[]) children.toArray(new WorkspaceElement[0]);
		for (int i = 0; i < tab.length; i++) {
			if(tab[i] instanceof ProofElement) {
				((ProofElement)tab[i]).compile(viewer);
			}
		}
	}
}
