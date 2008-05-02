package mobius.prover.gui.editor.outline;

import mobius.prover.gui.editor.outline.types.ProverType;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

/**
 * A class to provide image and label for a specific element of type
 * ProverType.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class TypeLabelProvider implements ILabelProvider {
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
    if (element instanceof ProverType) {
      return ((ProverType)element).getImage();
    }
    return null;
  }

  /** {@inheritDoc} */
  public String getText(final Object element) {
    if (element == null) {
      return "";
    }
    return element.toString();
  }

}
