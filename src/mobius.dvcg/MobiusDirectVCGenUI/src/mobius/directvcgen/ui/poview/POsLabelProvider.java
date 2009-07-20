package mobius.directvcgen.ui.poview;

import mobius.directvcgen.ui.poview.tree.AWorkspaceElement;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

/**
 * A label provider for elements that subclass the class 
 * {@link mobius.directvcgen.ui.poview.tree.AWorkspaceElement}.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class POsLabelProvider implements ILabelProvider {

  /** {@inheritDoc} */
  public void addListener(final ILabelProviderListener listener) {
  }

  /** {@inheritDoc} */
  public void dispose() {
  }

  /** {@inheritDoc} */
  public boolean isLabelProperty(final Object element, final String property) {
    return false;
  }

  /** {@inheritDoc} */
  public void removeListener(final ILabelProviderListener listener) {
  }

  /** {@inheritDoc} */
  public Image getImage(final Object element) {
    return ((AWorkspaceElement) element).getImage();
  }

  /** {@inheritDoc} */
  public String getText(final Object element) {
    return ((AWorkspaceElement) element).getName();
  }

}
