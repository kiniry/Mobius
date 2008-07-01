package mobius.directVCGen.ui.poview;

import mobius.directVCGen.ui.poview.tree.WorkspaceElement;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;


public class POsLabelProvider implements ILabelProvider {

	public void addListener(ILabelProviderListener listener) {
		// TODO Auto-generated method stub

	}

	public void dispose() {
		// TODO Auto-generated method stub

	}

	public boolean isLabelProperty(Object element, String property) {
		// TODO Auto-generated method stub
		return false;
	}

	public void removeListener(ILabelProviderListener listener) {
		// TODO Auto-generated method stub

	}

	public Image getImage(Object element) {
		return ((WorkspaceElement) element).getImage();
	}

	public String getText(Object element) {
		return ((WorkspaceElement) element).getName();
	}

}
