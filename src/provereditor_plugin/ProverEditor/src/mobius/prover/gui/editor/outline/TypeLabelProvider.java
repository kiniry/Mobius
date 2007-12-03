package mobius.prover.gui.editor.outline;

import mobius.prover.gui.editor.outline.types.ProverType;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;


public class TypeLabelProvider implements ILabelProvider {
  /** {@inheritDoc} */
  @Override
  public void addListener(final ILabelProviderListener listener) {

  }
  
  /** {@inheritDoc} */
  @Override
  public void dispose() {

  }
  
  /** {@inheritDoc} */
  @Override
  public boolean isLabelProperty(final Object element, final String property) {
    return false;
  }

  /** {@inheritDoc} */
  @Override
  public void removeListener(final ILabelProviderListener listener) {
  }
  
  /** {@inheritDoc} */
  @Override
  public Image getImage(final Object element) {
    if (element instanceof ProverType) {
      return ((ProverType)element).getImage();
    }
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public String getText(final Object element) {
    if (element == null) {
      return "";
    }
    return element.toString();
  }

}
