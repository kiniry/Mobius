package mobius.prover.gui.editor.outline;

import mobius.prover.gui.editor.outline.types.ProverType;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

/**
 * Provides the basic content of a node.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class TypeContentProvider implements ITreeContentProvider {
  /** an empty array of objects. */
  private static final Object[] EMPTY_ARRAY = new Object[0];

  /** {@inheritDoc} */
  public void dispose() {
    
  }
  
  /** {@inheritDoc} */
  public void inputChanged(final Viewer viewer, final Object oldInput, 
                           final Object newInput) {
  }
  
  /** {@inheritDoc} */
  public Object[] getChildren(final Object parent) {
    if (parent instanceof ProverType) {
      return ((ProverType)parent).getSubtypes();
    }
    return EMPTY_ARRAY;
  }
  
  /** {@inheritDoc} */
  public Object getParent(final Object elem) {
    if (elem instanceof ProverType) {
      return ((ProverType)elem).getSupertype();
    }
    return null;
  }
  
  /** {@inheritDoc} */
  public boolean hasChildren(final Object elem) {
    if (elem instanceof ProverType) {
      final Object[] os = ((ProverType)elem).getSubtypes();
      return (os != null) && (os.length > 0);
    }
    return false;
  }
  
  /** {@inheritDoc} */
  public Object[] getElements(final Object input) {
    return getChildren(input);
  }

}
