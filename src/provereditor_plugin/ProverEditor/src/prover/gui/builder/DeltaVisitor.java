package prover.gui.builder;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;

import prover.gui.builder.tagger.Tagger;


public class DeltaVisitor implements IResourceDeltaVisitor {

	public boolean visit(IResourceDelta delta) throws CoreException {
		IResource res = delta.getResource();
		int type = res.getType();
		Tagger tag = Tagger.instance;
		if(type == IResource.FILE) {
			switch(delta.getKind()) {
				case IResourceDelta.ADDED:
				case IResourceDelta.CHANGED:
					tag.performAddChangedFile((IFile) res);
					break;
				case IResourceDelta.REMOVED:
					tag.performRemoveFile((IFile) res);
					break;
				default:
					break;
			}
		}
		return true;
	}

}
