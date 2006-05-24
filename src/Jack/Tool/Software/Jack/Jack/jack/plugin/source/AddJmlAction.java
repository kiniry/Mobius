//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.source;

import jack.plugin.JackPlugin;
import jack.plugin.edit.SaveMessageDialog;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;

/**
 * Action allowing to generate JML specification.
 * 
 * @author L. Burdy
 */
public class AddJmlAction implements IObjectActionDelegate {

	/** The current selection. */
	IStructuredSelection selection;

	/** the current active part */
	IWorkbenchPart activePart;

	/**
	 * Constructor for Action1.
	 */
	public AddJmlAction() {
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
	 * Generates JML specifications for the selected compilation units.
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

		ICompilationUnit cu = (ICompilationUnit) selection.getFirstElement();

		LoadAndLink pog = new LoadAndLink(cu);

		AddJmlClauseWizard msd = new AddJmlClauseWizard(cu, pog);

		WizardDialog wd = new WizardDialog(site.getShell(), msd);
		wd.create();

		if (wd.open() == Window.OK)
			try {
				JavaUI.openInEditor(cu);
			} catch (Exception jme) {
				;
			}
//		Package.clearAll();
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
