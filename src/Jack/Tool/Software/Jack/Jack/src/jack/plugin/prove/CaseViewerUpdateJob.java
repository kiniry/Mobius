package jack.plugin.prove;

import jack.plugin.perspective.ICaseExplorer;

import java.io.IOException;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.progress.UIJob;

public class CaseViewerUpdateJob extends UIJob {
	ICaseExplorer ce;
	public CaseViewerUpdateJob(ICaseExplorer exp) {
		super("Updating Case Viewer");
		ce = exp;
	}
	
	public IStatus runInUIThread(IProgressMonitor monitor) {
		if(ce == null)
			return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
		TreeViewer tree = ce.getTree();
		try {
			ce.save();
		} catch (IOException e) {
			e.printStackTrace();
		}		
		tree.refresh();
		return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
	}
}
