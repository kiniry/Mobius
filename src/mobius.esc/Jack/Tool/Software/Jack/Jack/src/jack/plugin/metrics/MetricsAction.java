///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: OpenViewAction.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jack.plugin.metrics;

import jack.plugin.JackPlugin;
import jack.util.Logger;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.PartInitException;

/**
 * Action allowing openning the selection in the Jack PO viewer view.
 * @author L. Burdy
 */
public class MetricsAction implements IObjectActionDelegate {
	/** The current selection. */
	IStructuredSelection selection;
	/** the current active part */
	IWorkbenchPart activePart;

	private ICompilationUnit getCompilationUnit() {
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
		IWorkbenchPartSite site = activePart.getSite();
		IWorkbenchPage page = site.getPage();
		IViewPart view;

		try {
			view = page.showView(JackPlugin.JACK_METRICS_VIEW_ID);
		} catch (PartInitException e) {
			MessageDialog.openError(
				site.getShell(),
				JackPlugin.DIALOG_TITLE,
				"Error showing view: " + e.toString());
			return;
		}

		ICompilationUnit c = getCompilationUnit();
		if (c != null) {
			((MetricsView) view).setContent(c);
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
