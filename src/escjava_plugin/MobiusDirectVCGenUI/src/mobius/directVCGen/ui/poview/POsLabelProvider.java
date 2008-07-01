package mobius.directVCGen.ui.poview;

import mobius.directVCGen.ui.poview.tree.AWorkspaceElement;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;


public class POsLabelProvider implements ILabelProvider {

  public void addListener(final ILabelProviderListener listener) {
    // TODO Auto-generated method stub

  }

  public void dispose() {
    // TODO Auto-generated method stub

  }

  public boolean isLabelProperty(final Object element, final String property) {
    // TODO Auto-generated method stub
    return false;
  }

  public void removeListener(final ILabelProviderListener listener) {
    // TODO Auto-generated method stub

  }

  public Image getImage(final Object element) {
    return ((AWorkspaceElement) element).getImage();
  }

  public String getText(final Object element) {
    return ((AWorkspaceElement) element).getName();
  }

}
