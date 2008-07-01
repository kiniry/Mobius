package mobius.directVCGen.ui.poview.tree;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.TreeViewer;

public abstract class AProofElement extends AWorkspaceElement {
  
  public AProofElement(final IResource key) {
    super(key);
  }

  public void compile(final TreeViewer viewer) {
    final AWorkspaceElement [] tab = getElementChildren();
    for (int i = 0; i < tab.length; i++) {
      if (tab[i] instanceof AProofElement) {
        ((AProofElement)tab[i]).compile(viewer);
      }
    }
  }
}
