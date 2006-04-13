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

public abstract class AProverAction implements IWorkbenchWindowActionDelegate{

	private static Set set = new HashSet();
	public void dispose() {
		
	}

	public void init(IWorkbenchWindow window) {}

	public void selectionChanged(IAction action, ISelection selection) {
		set.add(action);
		action.setEnabled(isEnabled());
	}
	
	public static void setAllEnabled(boolean b) {
		Iterator i = set.iterator();
		while(i.hasNext()) {
			IAction a = (IAction)i.next();
			a.setEnabled(b);
		}
	}
	
	public boolean isEnabled() {
		IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IEditorPart ed = ap.getActiveEditor();
		if(ed instanceof ProverEditor) {
			return TopLevelManager.getInstance() != null;
		}
		return false;
	}
}
