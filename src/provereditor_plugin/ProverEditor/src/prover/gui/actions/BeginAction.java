package prover.gui.actions;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

import prover.gui.ProverFileContext;
import prover.gui.TopLevelManager;
import prover.gui.editor.ProverEditor;

/**
 * The action to start a new toplevel
 */
public class BeginAction extends AProverAction{
	
	/*
	 * (non-Javadoc)
	 * @see prover.gui.actions.AProverAction#trigger()
	 */
	public void trigger() {
		try {
			PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView("ProverEditor.topview");
		} catch (PartInitException e) {	}
		IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IEditorPart ed = ap.getActiveEditor();
		if(ed instanceof ProverEditor) {
			TopLevelManager ctm = TopLevelManager.getInstance();
			if(ctm != null)
				ctm.reset(new ProverFileContext((ProverEditor)ed));
		}
	}
	
	/*
	 *  (non-Javadoc)
	 * @see prover.gui.actions.AProverAction#isEnabled()
	 */
	public boolean isEnabled() {
		IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IEditorPart ed = ap.getActiveEditor();
		return (ed instanceof ProverEditor); 
	}
	
}
