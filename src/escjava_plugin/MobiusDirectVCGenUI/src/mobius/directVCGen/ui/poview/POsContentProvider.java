package mobius.directVCGen.ui.poview;

import mobius.directVCGen.ui.poview.tree.Project;
import mobius.directVCGen.ui.poview.tree.WorkspaceElement;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;


public class POsContentProvider implements ITreeContentProvider {
  
  private static final class ChangeListener implements IResourceChangeListener {
    private final TreeViewer fViewer;
    public ChangeListener(final TreeViewer viewer) {
      fViewer = viewer;
    }

    public void resourceChanged(final IResourceChangeEvent event) {
      final IResourceDelta deltas =  event.getDelta();
      try {
        deltas.accept(new ChangeVisitor(fViewer));
      } 
      catch (CoreException e) {
        e.printStackTrace();
      }
    
    }
  }

  private static final class ChangeVisitor implements IResourceDeltaVisitor {
    private final TreeViewer fViewer;
    
    public ChangeVisitor(final TreeViewer viewer) {
      fViewer = viewer;
    }

    public boolean visit(final IResourceDelta delta) throws CoreException {
      final IResource res = delta.getResource();
      WorkspaceElement pe = WorkspaceElement.getElement(res);
      if (pe == null && res instanceof IFile) {
        pe = WorkspaceElement.getElement(res.getParent());
        final WorkspaceElement [] os = pe.getElementChildren();
        for (int i = 0; i < os.length; i++) {
          String name = res.getName();
          name = name.substring(0, name.length() - 2);
          if (os[i].getName().startsWith(name)) {
            pe = os[i];
          }
        }
      }
      
      if (res instanceof IProject) {
        switch (delta.getKind()) {
          case IResourceDelta.ADDED:
          case IResourceDelta.REMOVED:
            fViewer.setInput(Utils.getProjects());
            return true;
          default:
            break;
        }
      }
      if (pe == null) {
        return true;
      }
      switch (delta.getKind()) {
        case IResourceDelta.ADDED:
          pe.getParent().update();
          Utils.refreshTree(fViewer, pe.getParent());
          break;
        case IResourceDelta.REMOVED:
          pe.getParent().update();
          Utils.refreshTree(fViewer, pe.getParent());
          break;
        case IResourceDelta.CHANGED:
          pe.update();
          Utils.refreshTree(fViewer, pe);
          break;
        default:
          break;
      }
      return true;
    }
  }

  public POsContentProvider(final TreeViewer viewer) {
    final IWorkspace workspace = ResourcesPlugin.getWorkspace();
    final IResourceChangeListener listener = new ChangeListener(viewer);
    workspace.addResourceChangeListener(listener);
  }
  public void dispose() {
     
  }

  public void inputChanged(final Viewer viewer, final Object oldInput, final Object newInput) {
    if (oldInput == null) {
      return;
    }
    final Project[] tab  = (Project[]) oldInput;
    for (int i = 0; i < tab.length; i++) {
      tab[i].remove();
    }
  }

  public Object[] getElements(final Object input) {
    return (Object[]) input;
  }



  public Object[] getChildren(final Object elem) {
    return ((WorkspaceElement) elem).getChildren();
  }

  public Object getParent(final Object elem) {
    return ((WorkspaceElement) elem).getParent();
  }

  public boolean hasChildren(final Object elem) {
    return ((WorkspaceElement) elem).getChildrenCount() > 0;
  }
}
