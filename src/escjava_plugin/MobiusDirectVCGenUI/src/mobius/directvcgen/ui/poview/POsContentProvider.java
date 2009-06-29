package mobius.directvcgen.ui.poview;

import mobius.directvcgen.ui.poview.tree.AWorkspaceElement;
import mobius.directvcgen.ui.poview.tree.Project;
import mobius.directvcgen.ui.poview.util.RefreshUtils;

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
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;


/**
 * A content provider for the tree view.
 * It is a content provider to use with the  
 * {@link mobius.directvcgen.ui.poview.tree.AWorkspaceElement}.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class POsContentProvider implements ITreeContentProvider {
  /** The current tree viewer content.  */
  private Project[] fCurrent;
  private IProject [] fInput;
  
  /**
   * Construct a content provider, providing its corresponding viewer.
   * @param viewer the viewer this content provider is used with 
   */
  public POsContentProvider(final TreeViewer viewer) {
    final IWorkspace workspace = ResourcesPlugin.getWorkspace();
    final IResourceChangeListener listener = new ChangeListener(viewer);
    workspace.addResourceChangeListener(listener);
  }
  
  /** {@inheritDoc} */
  public void dispose() { }
  
 /** {@inheritDoc} */
  public void inputChanged(final Viewer viewer, final Object oldInput, final Object newInput) {
    if (newInput == null || newInput.equals(fInput)) {
      return;
    }
    fInput = (IProject[]) newInput;
    try {
      fCurrent = AWorkspaceElement.createProjectItem((IProject[]) newInput);
    }
    catch (IllegalArgumentException e) {
      e.printStackTrace();
    }
    viewer.refresh();
  }

  /** {@inheritDoc} */
  public Object[] getElements(final Object input) {
    return (Object[]) fCurrent;
  }



  /** {@inheritDoc} */
  public Object[] getChildren(final Object elem) {
    if (elem instanceof AWorkspaceElement) {
      return ((AWorkspaceElement) elem).getChildren();
    }
    else {
      return (Object[]) fCurrent;
    }
  }

  /** {@inheritDoc} */
  public Object getParent(final Object elem) {
    return ((AWorkspaceElement) elem).getParent();
  }

  /** {@inheritDoc} */
  public boolean hasChildren(final Object elem) {
    return ((AWorkspaceElement) elem).getChildrenCount() > 0;
  }
  
  /**
   * A listener to be aware of the changes of a specific resource (most likely a project).
   * It nodifies the viewer associociated to it just in case.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  private static final class ChangeListener implements IResourceChangeListener {
    /** the current viewer associated with this change listener. */
    private final TreeViewer fViewer;
    
    /**
     * Constructs a listener.
     * @param viewer the viewer which shall be notified
     */
    public ChangeListener(final TreeViewer viewer) {
      fViewer = viewer;
    }

    /** {@inheritDoc} */
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

  /**
   * A visitor to inspect the changes that were done on a resource.
   * 
   * @author J. Charles (julien.charles@inria.fr)
   */
  private static final class ChangeVisitor implements IResourceDeltaVisitor {
    /** the viewer associated with this visitor. */
    private final TreeViewer fViewer;
    
    /**
     * Construct the visitor.
     * @param viewer a valid viewer that will be notified of the changes.
     */
    public ChangeVisitor(final TreeViewer viewer) {
      fViewer = viewer;
    }

    /** {@inheritDoc} */
    public boolean visit(final IResourceDelta delta) throws CoreException {
      final IResource res = delta.getResource();

      if (res instanceof IProject) { // first let's handle the project case
        switch (delta.getKind()) {
          case IResourceDelta.ADDED:
            fViewer.setInput(new IProject[]{(IProject)res});
            RefreshUtils.refreshTree(fViewer);
            break;
          case IResourceDelta.REMOVED:
            fViewer.setInput(new IProject[0]);
            RefreshUtils.refreshTree(fViewer);
                  // no more projects selected  
          default:
            break;
        }
        return true;
      }
      
      final AWorkspaceElement pe = getNodeFromRes(res);
      
      if (pe != null) {
        switch (delta.getKind()) {
          case IResourceDelta.ADDED:
            pe.getParent().update();
            RefreshUtils.refreshTree(fViewer, pe.getParent());
            break;
          case IResourceDelta.REMOVED:
            pe.getParent().update();
            RefreshUtils.refreshTree(fViewer, pe.getParent());
            break;
          case IResourceDelta.CHANGED:
            pe.update();
            RefreshUtils.refreshTree(fViewer, pe);
            break;
          default:
            break;
        }
      }
      return true;
    }

    /**
     * Returns the node corresponding to the resource or null if it miserably fails.
     * @param res the resource to get the node from
     * @return a valid node or null if nothing was found
     */
    private AWorkspaceElement getNodeFromRes(final IResource res) {
      AWorkspaceElement pe = AWorkspaceElement.getElement(res);      
      if (pe == null) { // we try to be more specific
        pe = AWorkspaceElement.getElement(res.getParent());
        if (pe == null) { // we are a total failure
          return null;
        }
        final AWorkspaceElement [] os = pe.getElementChildren();
        for (int i = 0; i < os.length; i++) {
          String name = res.getName();
          final String ext = "" + res.getFileExtension();
          name = name.substring(0, name.length() - ext.length());
          if (os[i].getName().startsWith(name)) {
            pe = os[i];
          }
        }
      }
      return pe;
    }
  }


}
