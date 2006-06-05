//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package propagation;

import jack.util.Logger;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;

/**
 * Action allowing openning the selection in the Jack PO viewer view.
 * @author L. Burdy
 */
public class PropagateAction implements IObjectActionDelegate {
	/** The current selection. */
	IStructuredSelection selection;
	/** the current active part */
	IWorkbenchPart activePart;

	private IFile getIFile() {
		if (selection.isEmpty()) {
			return null;
		}
		try {
			return (IFile) selection.getFirstElement();
		} catch (ClassCastException e) {
			Logger.get().println(this, 
				"OpenViewAction.getCompilationUnit: "
					+ "error casting selection to ICompilationUnit");
			return null;
		}
	}

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
//		Package.clearAll();
		IWorkbenchPartSite site = activePart.getSite();
		IFile ifi = getIFile();
		if (ifi != null) {
			PropagationWizard pw = new PropagationWizard(ifi);

			WizardDialog wd = new WizardDialog(site.getShell(), pw);
			wd.create();

			wd.open();

//			Package.clearAll();
		}
	}

	/**
	 * @see org.eclipse.ui.IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
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
			MessageDialog.openError(
				activePart.getSite().getShell(),
				"Jack Error",
				"Unexpected selection type: expected StructuredSelection, "
					+ "got "
					+ sel.getClass().getName());
		}

	}

}