package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;


public class Project extends ProofElement {
	String name;
	private IProject project;
	public Project(IProject project) {
		super(project);
		name = project.getName();
		this.project = project;
		update();
	}
	
	public void update() {
		IFolder f = project.getFolder("coq_proofs");
		
		IResource[] res = new IResource[0];
		if(f.exists()) {
			try {
				res = f.members(IResource.NONE);
			} catch (CoreException e) {
				e.printStackTrace();
			}
		}
		update(res);
	}



	public WorkspaceElement createChildFromResource(IResource res) {
		WorkspaceElement pe = null;
		if(res instanceof IFolder) {
			pe = new TargetClass((IFolder) res);
		}
		if(res instanceof IFile) {
			IFile f = (IFile) res;
			if(!f.getName().endsWith(".v"))
				return null;
			pe = new LibFile((IFile) res);
		}
		return pe;
	}
	
	public String getName() {
		return name;
	}
	public String toString() {
		return "Project: " + getName();
	}

	public IProject getProject() {
		return project;
	}
	public Image getImage () {
		if(this.getChildrenCount() > 0)
			return Utils.getImage(IMG_PROJECT);
		else 
			return Utils.getImage(IMG_PROJECT_EMPTY);
	}

}
