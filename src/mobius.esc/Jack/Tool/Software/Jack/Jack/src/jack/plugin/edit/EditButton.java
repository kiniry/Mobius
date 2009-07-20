//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: EditButton.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.edit;

import jack.plugin.JackPlugin;
import jack.plugin.ToolbarButton;
import jack.util.Logger;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PartInitException;

/**
 * Button allowing to "edit" the selected JML file.
 * <p>
 * If several JML files are selected, then one of them is chosen.
 * @author A. Requet, L. Burdy
 */
public class EditButton extends ToolbarButton {
	/**
	 * Returns the compilation unit that is selected.
	 */
	private ICompilationUnit getCompilationUnit() {
		IStructuredSelection selection = getSelection();
		if (selection.isEmpty()) {
			return null;
		}
		try {
			return (ICompilationUnit) selection.getFirstElement();
		} catch (ClassCastException e) {
			Logger.err.println(
				"OpenViewAction.getCompilationUnit: "
					+ "error casting selection to ICompilationUnit");
			return null;
		}
	}

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		Shell shell = getWindow().getShell();

		try {
			getWindow().getActivePage().showView(JavaUI.ID_PACKAGES);
		} catch (PartInitException e) {
			MessageDialog.openError(
				shell,
				JackPlugin.DIALOG_TITLE,
				"Error showing view: " + e.toString());
			return;
		}

		if (getSelection() == null) {
			MessageDialog.openInformation(
				shell,
				JackPlugin.DIALOG_TITLE,
				"You should select a JML file first");
			return;
		}

		EditAction.edit(getCompilationUnit());
	}
}
