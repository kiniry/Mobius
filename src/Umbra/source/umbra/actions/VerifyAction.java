package umbra.actions;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;

/**
 * The action is used to convert Java Bytecode into BoogiePL.
 * 
 * @author Samuel Willimann
 *
 */
public class VerifyAction implements IEditorActionDelegate {
	
	/**
	 * TODO
	 */
	private IEditorPart editor;

	/**
	 * TODO
	 */
	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		editor = targetEditor;
	}

	/**
	 * TODO
	 */
	public void run(IAction action) {
		
		// TODO convert Bytecode to BoogiePL
		
		// TODO Run Boogie on the generated BoogiePL program
		
		return;
	}

	/**
	 * TODO
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		// TODO Auto-generated method stub

	}

}