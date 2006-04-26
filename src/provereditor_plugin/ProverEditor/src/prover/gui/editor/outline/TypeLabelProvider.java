package prover.gui.editor.outline;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

import prover.gui.editor.outline.types.ProverType;

public class TypeLabelProvider implements ILabelProvider {

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
		if(element instanceof ProverType) {
			return ((ProverType)element).getImage();
		}
		return null;
	}

	public String getText(Object element) {
		if (element == null) {
			return "";
		}
		return element.toString();
	}

}
