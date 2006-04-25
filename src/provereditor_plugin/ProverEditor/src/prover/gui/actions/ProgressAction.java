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

/**
 * An action to progress in ProverEditor.
 */
public class ProgressAction extends AProverAction  {

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
	 */
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
	
	/**
	 * The Job to send a progress action to the top level.
	
	 */
	private class UpdateJob extends Job {
		/** The target editor where to progress */
		private ProverEditor fEditor;
		
		/**
		 * Create a new Job to progress.
		 * @param editor The target editor
		 */
		public UpdateJob(ProverEditor editor) {
			super("TopLevel is progressing...");
			fEditor = editor;
		}	
		
		/*
		 *  (non-Javadoc)
		 * @see org.eclipse.core.internal.jobs.InternalJob#run(org.eclipse.core.runtime.IProgressMonitor)
		 */
		public IStatus run(IProgressMonitor monitor) {
			try {
				TopLevelManager.getInstance().progress(new ProverFileContext(fEditor));
			}
			catch(Exception e) {
				e.printStackTrace();
			}
			return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
		}
	}
}
