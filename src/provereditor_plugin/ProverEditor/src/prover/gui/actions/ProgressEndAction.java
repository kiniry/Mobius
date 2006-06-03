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
import org.eclipse.ui.progress.UIJob;

import prover.gui.ProverFileContext;
import prover.gui.TopLevelManager;
import prover.gui.editor.ProverEditor;

/**
 * An action to progress until the end of the file.
 */
public class ProgressEndAction  extends AProverAction {
	/** the target editor */
	private ProverEditor fEditor;

	public void run(IAction action) {
		try {
			PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView("ProverEditor.topview");
		} catch (PartInitException e) {	}
		IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IEditorPart editor = ap.getActiveEditor();
		if(editor instanceof ProverEditor) {
			fEditor = (ProverEditor) editor;
			Job j = new Job("TopLevel Editor is computing...") {
				/*
				 *  (non-Javadoc)
				 * @see org.eclipse.core.internal.jobs.InternalJob#run(org.eclipse.core.runtime.IProgressMonitor)
				 */
				protected IStatus run(IProgressMonitor monitor) {
					boolean notlastres = true;
					if(TopLevelManager.getInstance() == null)
						System.out.println("nul");
					while (notlastres) {
						notlastres = TopLevelManager.getInstance().progress( new ProverFileContext(fEditor));
						UIJob job = new UIJob("CoqEditor is updating..."){
							public IStatus runInUIThread(IProgressMonitor monitor) {
								return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
							}
						};
						job.schedule();
						try {
							job.join();
						
						} catch (InterruptedException e) {
							e.printStackTrace();
						}
					}
					return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
				}
				
			};
			j.schedule();		
		}		
	}
}
