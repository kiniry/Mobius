package mobius.prover.gui.actions;

import mobius.prover.gui.TopLevelManager;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

import prover.gui.editor.ProverEditor;

/**
 * The action that send a break command to the top level.
 */
public class BreakAction extends AProverAction {
	
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
			TopLevelManager.getInstance().doBreak();			
		}
	}

}
