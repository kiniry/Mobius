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
		private TreeViewer viewer;
		public ChangeListener(TreeViewer viewer) {
			this.viewer = viewer;
		}

		public void resourceChanged(IResourceChangeEvent event) {
			IResourceDelta deltas =  event.getDelta();
			try {
				deltas.accept(new ChangeVisitor(viewer));
			} catch (CoreException e) {
				e.printStackTrace();
			}
		
		}
	}

	private final static class ChangeVisitor implements IResourceDeltaVisitor {
		private TreeViewer viewer;
		public ChangeVisitor(TreeViewer viewer) {
			this.viewer = viewer;
		}

		public boolean visit(IResourceDelta delta) throws CoreException {
			IResource res = delta.getResource();
			WorkspaceElement pe = WorkspaceElement.getElement(res);
			if(pe == null && res instanceof IFile) {
				pe = WorkspaceElement.getElement(res.getParent());
				WorkspaceElement [] os = pe.getElementChildren();
				for (int i = 0; i < os.length; i++) {
					String name = res.getName();
					name = name.substring(0, name.length() - 2);
					if(os[i].getName().startsWith(name)) {
						pe = os[i];
					}
				}
			}
			
			if(res instanceof IProject) {
				switch (delta.getKind()) {
					case IResourceDelta.ADDED:
					case IResourceDelta.REMOVED:
						viewer.setInput(Utils.getProjects());
						return true;
					default:
						break;
				}
			}
			if(pe == null)
				return true;
			switch (delta.getKind()) {
				case IResourceDelta.ADDED:
					pe.getParent().update();
					Utils.refreshTree(viewer, pe.getParent());
					break;
				case IResourceDelta.REMOVED:
					pe.getParent().update();
					Utils.refreshTree(viewer, pe.getParent());
					break;
				case IResourceDelta.CHANGED:
					pe.update();
					Utils.refreshTree(viewer, pe);
					break;
				default:
					break;
			}
			return true;
		}
	}

	public POsContentProvider(TreeViewer viewer) {
		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IResourceChangeListener listener = new ChangeListener(viewer);
	    workspace.addResourceChangeListener(listener);
	}
	public void dispose() {
 		
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if(oldInput == null)
			return;
		Project[] tab  = (Project[]) oldInput;
		for (int i = 0 ; i < tab.length; i++) {
			tab[i].remove();
		}
	}

	public Object[] getElements(Object input) {
		return (Object[]) input;
	}



	public Object[] getChildren(Object elem) {
		return ((WorkspaceElement) elem).getChildren();
	}

	public Object getParent(Object elem) {
		return ((WorkspaceElement) elem).getParent();
	}

	public boolean hasChildren(Object elem) {
		return ((WorkspaceElement) elem).getChildrenCount() > 0;
	}
}
