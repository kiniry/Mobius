package mobius.prover.gui.editor.outline;

import mobius.prover.gui.editor.outline.types.ProverType;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;


public class TypeContentProvider implements ITreeContentProvider {
  private static final Object[] EMPTY_ARRAY = new Object[0];

  /** {@inheritDoc} */
  @Override
  public void dispose() {
    
  }
  
  /** {@inheritDoc} */
  @Override
  public void inputChanged(final Viewer viewer, final Object oldInput, 
                           final Object newInput) {
  }
  
  /** {@inheritDoc} */
  @Override
  public Object[] getChildren(final Object parent) {
    if (parent instanceof ProverType) {
      return ((ProverType)parent).getSubtypes();
    }
    return EMPTY_ARRAY;
  }
  
  /** {@inheritDoc} */
  @Override
  public Object getParent(final Object elem) {
    if (elem instanceof ProverType) {
      return ((ProverType)elem).getSupertype();
    }
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public boolean hasChildren(final Object elem) {
    if (elem instanceof ProverType) {
      final Object[] os = ((ProverType)elem).getSubtypes();
      return (os != null) && (os.length > 0);
    }
    return false;
  }
  
  /** {@inheritDoc} */
  @Override
  public Object[] getElements(final Object input) {
    return getChildren(input);
  }

}
