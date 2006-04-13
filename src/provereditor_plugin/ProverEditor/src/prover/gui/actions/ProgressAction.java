package prover.gui.actions;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

import prover.gui.ProverFileContext;
import prover.gui.TopLevelManager;
import prover.gui.editor.ProverEditor;

public class ProgressAction  
	extends AProverAction  {

	
	public void run(IAction action) {
		try {
			PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView("CoqEditor.coqtopview");
		} catch (PartInitException e) {	}
		IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IEditorPart ed = ap.getActiveEditor();
		if(ed instanceof ProverEditor) {
			ProverEditor ce = (ProverEditor) ed;
			Job job = new UpdateJob(ce);
			job.schedule();
			
		}
		
	}
	private class UpdateJob extends Job {
		private ProverEditor ce;
		public UpdateJob(ProverEditor ce) {
			super("TopLevel is progressing...");
			this.ce = ce;
		}

		public IStatus run(IProgressMonitor monitor) {
			try {
				TopLevelManager.getInstance().progress(new ProverFileContext(ce));
			}
			catch(Exception e) {
				e.printStackTrace();
			}
			return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
		}

		
		
	}
	
}
