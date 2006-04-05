package prover.gui.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

import prover.gui.ProverContext;
import prover.gui.TopLevelManager;
import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.BasicSourceViewerConfig;
import prover.gui.editor.ProverEditor;


/**
 * This Class trigger an action to reset the current proof.
 * @author jcharles
 *
 */
public class ResetAction extends AProverAction{



	public void run(IAction action) {
		try {
			PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView("CoqEditor.coqtopview");
		} catch (PartInitException e) {	}
		IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IEditorPart ed = ap.getActiveEditor();
		if(! (ed instanceof ProverEditor))
			return;
		ProverEditor ce = (ProverEditor) ed;
		BasicSourceViewerConfig sv = ce.getSourceViewerConfig();
		BasicRuleScanner scan = sv.getTagScanner();
		IDocument doc = sv.getPresentationReconciler().getDocument();
		TopLevelManager.getInstance().reset(new ProverContext(ce, doc, sv, scan));		

		
	}
	
}
