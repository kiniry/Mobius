package prover.gui.actions;

import org.eclipse.core.commands.IHandlerListener;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.core.commands.IHandler;

/**
 * A class to implement the basic functions of a handler which might be
 * useless for our purpose(s)...
 * @author J. Charles
 *
 */
public abstract class AJumpAction implements IHandler{
	/**
	 * For now there is no property associated with the jump action.
	 * The handle listener are useless.
	 */
	public void addHandlerListener(IHandlerListener handlerListener) { }
	/**
	 * For now there is no property associated with the jump action.
	 * The handle listener are useless.
	 */
	public void removeHandlerListener(IHandlerListener handlerListener) { }
	
	
	/**
	 * Returns the current active editor of the workbench.
	 * It has the same result as {@link PlatformUI#getWorkbench()#getActiveWorkbenchWindow()#getActivePage()#getActiveEditor()}
	 * @return The active editor
	 */
	protected static IEditorPart getActiveEditor() {
		return PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
	}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.core.commands.IHandler#isEnabled()
	 */
	public boolean isEnabled() {
		return true;
	}

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.core.commands.IHandler#isHandled()
	 */
	public boolean isHandled() {
		return true;
	}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.core.commands.IHandler#dispose()
	 */
	public void dispose() { }
}
