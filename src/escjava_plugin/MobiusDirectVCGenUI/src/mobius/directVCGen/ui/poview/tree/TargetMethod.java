package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;


public class TargetMethod extends ProofElement {

	IFolder folder;
	public TargetMethod(IFolder folder) {
		super(folder);
		this.folder = folder;
		update();
	}
	public void update() {
		IResource[] res = new IResource[0];
		try {
			res = folder.members(IResource.NONE);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		update(res);
	
	}
	public WorkspaceElement createChildFromResource(IResource res) {
		WorkspaceElement pe = null;
		if((res instanceof IFile) && res.toString().endsWith(".v")) {
			pe = new Goal((IFile) res);
		}
		return pe;
	}
	

	
	
	public String getName() {
		return folder.getName();
	}
	
	public Image getImage () {
		return  Utils.getImage(IMG_METHOD);
	}
}
