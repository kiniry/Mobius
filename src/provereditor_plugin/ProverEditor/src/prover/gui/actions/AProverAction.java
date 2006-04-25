package prover.gui.actions;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PlatformUI;

import prover.gui.TopLevelManager;
import prover.gui.editor.ProverEditor;

/**
 * Action used for the toolbar buttons provided by ProverEditor.
 */
public abstract class AProverAction implements IWorkbenchWindowActionDelegate{
	/** The set of all the actions of type {@link AProverAction} */
	private static Set fSet = new HashSet();
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchWindowActionDelegate#init(org.eclipse.ui.IWorkbenchWindow)
	 */
	public void init(IWorkbenchWindow window) {}
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchWindowActionDelegate#dispose()
	 */
	public void dispose() {}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		fSet.add(action);
		action.setEnabled(isEnabled());
	}
	
	
	/**
	 * Call on all actions implementing AProverAction the method
	 * {@link IAction#setEnabled(boolean)}. With the value of
	 * <code>b</code> as parameter.
	 * @param b Whether or not it the actions shall be enabled
	 */
	public static void setAllEnabled(boolean b) {
		Iterator i = fSet.iterator();
		while(i.hasNext()) {
			IAction a = (IAction)i.next();
			a.setEnabled(b);
		}
	}
	
	/**
	 * Tell whether or not the action shall be enabled.
	 * @return <code>true</code> if the action shall be enabled.
	 */
	public boolean isEnabled() {
		IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IEditorPart ed = ap.getActiveEditor();
		if(ed instanceof ProverEditor) {
			return TopLevelManager.getInstance() != null;
		}
		return false;
	}
}
