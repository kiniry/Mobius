package mobius.directVCGen.ui.poview.tree;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.TreeViewer;

public abstract class ProofElement extends WorkspaceElement {
  public ProofElement(final IResource key) {
    super(key);
  }

  public void compile(final TreeViewer viewer) {
    final WorkspaceElement [] tab = children.toArray(new WorkspaceElement[0]);
    for (int i = 0; i < tab.length; i++) {
      if (tab[i] instanceof ProofElement) {
        ((ProofElement)tab[i]).compile(viewer);
      }
    }
  }
}
