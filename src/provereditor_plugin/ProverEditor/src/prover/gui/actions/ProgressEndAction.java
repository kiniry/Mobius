package prover.gui.actions;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;

import prover.gui.TopLevelManager;
import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.BasicSourceViewerConfig;
import prover.gui.editor.ProverEditor;

public class ProgressEndAction  extends AProverAction {
	private BasicSourceViewerConfig sv;
	private BasicRuleScanner scan;
	private IDocument doc;
	private FindReplaceDocumentAdapter fda;
	private ProverEditor ce;

	public void run(IAction action) {
		try {
			PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView("CoqEditor.coqtopview");
		} catch (PartInitException e) {	}
		IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IEditorPart ed = ap.getActiveEditor();
		if(ed instanceof ProverEditor) {
			ce = (ProverEditor) ed;
			
			sv = ce.getSourceViewerConfig();
			scan = sv.getTagScanner();
			
			doc = sv.getPresentationReconciler().getDocument();
			fda = sv.getPresentationReconciler().getFinder();
			
			Job j = new Job("TopLevel Editor is computing...") {
				boolean lastres;
				protected IStatus run(IProgressMonitor monitor) {
					lastres = true;
					if(TopLevelManager.getInstance() == null)
						System.out.println("nul");
					while (lastres) {
						lastres = TopLevelManager.getInstance().progress( ce, doc, fda, sv, scan);
						UIJob job = new UIJob("CoqEditor is updating..."){
							public IStatus runInUIThread(IProgressMonitor monitor) {
								sv.getPresentationReconciler().everythingHasChanged();
								TopLevelManager.getInstance().printMsg();
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
