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

import prover.gui.TopLevelManager;
import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.BasicSourceViewerConfig;
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
			
			BasicSourceViewerConfig sv = ce.getSourceViewerConfig();
			BasicRuleScanner scan = sv.getTagScanner();
			
			IDocument doc = sv.getPresentationReconciler().getDocument();
			FindReplaceDocumentAdapter fda = sv.getPresentationReconciler().getFinder();
			Job job = new UpdateJob(ce, sv, scan, doc, fda);
			job.schedule();
			
		}
		
	}
	private class UpdateJob extends Job {
		BasicSourceViewerConfig sv; BasicRuleScanner scan;
		IDocument doc;FindReplaceDocumentAdapter fda;
		private ProverEditor ce;
		public UpdateJob(ProverEditor ce, BasicSourceViewerConfig sv, BasicRuleScanner scan,
		IDocument doc,FindReplaceDocumentAdapter fda) {
			super("Coq is progressing...");
			this.doc = doc;
			this.fda = fda;
			this.scan = scan;
			this.sv = sv;
			this.ce = ce;
		}

		public IStatus run(IProgressMonitor monitor) {
			try {
				TopLevelManager.getInstance().progress(ce, doc, fda, sv, scan);
			}
			catch(Exception e) {
				e.printStackTrace();
			}
			return new Status(IStatus.OK, Platform.PI_RUNTIME, IStatus.OK, "", null);
		}

		
		
	}
	
}
