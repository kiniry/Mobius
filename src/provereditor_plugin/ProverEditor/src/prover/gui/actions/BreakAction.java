package prover.gui.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

import prover.gui.TopLevelManager;
import prover.gui.editor.ProverEditor;

/**
 * The action that send a break command to the top level.
 * @author J. Charles
 */
public class BreakAction extends AProverAction {
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
			TopLevelManager.getInstance().doBreak();			
		}
	}

}
