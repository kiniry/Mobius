//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JackPopup.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.compile;

import jack.plugin.JackPlugin;
import jack.plugin.edit.SaveMessageDialog;
import jack.util.Logger;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;

/**
 * Popup action that allows to generate <code>.jpo</code> files when a java file is
 * selected.
 * @author A. Requet, L. Burdy
 */
public class VerifySourceAction implements IObjectActionDelegate {
	
	/** The current selection. */
	IStructuredSelection selection;
	
	/** the current active part */
	IWorkbenchPart activePart;

	/**
	 * Constructor for Action1.
	 */
	public VerifySourceAction() {
		super();
	}

	/**
	 * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
	 *		Sets the active part for the delegate.  
		 * The active part is commonly used to get a working context for the action,
		 * such as the shell for any dialog which is needed.
	 * <p>
	 * This method will be called every time the action appears in a popup menu.  The
	 * targetPart may change with each invocation.
	 * </p>
	 *
	 * @param action the action proxy that handles presentation portion of the action
	 * @param targetPart the new part target
	 */
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		activePart = targetPart;
	}

	/**
	 * Generates Proof Obligations for the selected compilation units.
	 * 
	 * @see IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		IWorkbenchPartSite site = activePart.getSite();

		if (selection == null) {
			MessageDialog.openInformation(
				site.getShell(),
				JackPlugin.DIALOG_TITLE,
				"Error: Selection is null");
			return;
		}

		if (!SaveMessageDialog
			.saveModifiedRessources(
				activePart,
				"compiling",
				JackPlugin.ALWAYS_SAVE_BEFORE_COMPILING))
			return;

		PoGenerator pog = new PoGenerator(selection.iterator());

		ProgressMonitorDialog dlg = new ProgressMonitorDialog(site.getShell());

		try {
			dlg.run(true, true, pog);
		} catch (InvocationTargetException e) {
			Throwable t = e.getTargetException();
			Logger.err.println("InvocationTargetException : " + t.toString());
			t.printStackTrace();
			MessageDialog.openInformation(
				site.getShell(),
				JackPlugin.DIALOG_TITLE,
				"InvocationTargetException catched : " + t.toString());
		} catch (Exception e) {
			MessageDialog.openInformation(
				site.getShell(),
				JackPlugin.DIALOG_TITLE,
				"Exception catched (JackPopup.run()): " + e.toString());
			return;
		}

		// in case of error, explain why
		if (!pog.hasSucceeded()) {
			MessageDialog.openInformation(
				site.getShell(),
				JackPlugin.DIALOG_TITLE,
				pog.getErrorDescription());
		}
	}

	/**
	 * Update the selection accordingly to the selection changes within the
	 * editor.
	 * 
	 * @see IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		if (selection instanceof IStructuredSelection) {
			this.selection = (IStructuredSelection) selection;
		} else {
			MessageDialog.openError(
				activePart.getSite().getShell(),
				"Jack Error",
				"Unexpected selection type: expected StructuredSelection, "
					+ "got "
					+ selection.getClass().getName());
		}
	}

}
