package mobius.prover.gui.actions;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;


/**
 * The action to send a back command to the toplevel.
 */
public class BackAction extends AProverAction{

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
			ProverEditor ce = (ProverEditor) ed;
			TopLevelManager.getInstance().regress(new ProverFileContext(ce));			
		}
	}
}
