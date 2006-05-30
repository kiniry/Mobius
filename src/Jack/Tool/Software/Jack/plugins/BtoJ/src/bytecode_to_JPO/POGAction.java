//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package bytecode_to_JPO;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

/**
 * Action allowing openning the selection in the Jack PO viewer view.
 * 
 * @author L. Burdy
 */
public class POGAction implements IObjectActionDelegate {
	/** The current selection. */
	IStructuredSelection selection;

	/** the current active part */
	IWorkbenchPart activePart;

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		ProgressMonitorDialog pmd = new ProgressMonitorDialog(activePart.getSite().getShell());
		POGGenerator pg = new POGGenerator(selection.getFirstElement());
		try {
			pmd.run(false, false, pg);
		} catch (InterruptedException ie) {
		} catch (InvocationTargetException ie) {
		}

	}

	/**
	 * @see org.eclipse.ui.IObjectActionDelegate#setActivePart(IAction,
	 *          IWorkbenchPart)
	 */
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		activePart = targetPart;
	}

	/**
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection sel) {
		if (sel instanceof IStructuredSelection) {
			this.selection = (IStructuredSelection) sel;
		} else {
			// should never happen
			MessageDialog.openError(activePart.getSite().getShell(),
									"Jack Error",
									"Unexpected selection type: expected StructuredSelection, " + "got "
			+ sel.getClass().getName());
		}

	}

}