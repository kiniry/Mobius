package mobius.rcp;

import org.eclipse.core.commands.*;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.update.ui.UpdateManagerUI;

/**
 * This handler is hooked to a command provided by the application (such
 * as org.eclipse.ui.ide). This allows RCP applications to control how update
 * functionality is surfaced.
 */
public class FindAndInstallHandler extends AbstractHandler {

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
	  System.out.println("hey");
		UpdateManagerUI.openInstaller(HandlerUtil.getActiveShell(event));
		return null;
	}

}