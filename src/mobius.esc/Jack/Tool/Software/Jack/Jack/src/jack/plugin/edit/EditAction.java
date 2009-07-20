//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: OpenViewAction.java
 /*
 /********************************************************************************
 /* Warnings/Remarks:
 /*******************************************************************************/
package jack.plugin.edit;

import jack.plugin.JackPlugin;
import jack.plugin.compile.*;
import jack.plugin.perspective.CaseExplorer;
import jack.plugin.perspective.SourceCaseViewer;

import org.eclipse.core.resources.IFile;
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
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.WorkbenchException;

/**
 * Action allowing openning the selection in the Jack PO viewer view.
 * 
 * @author L. Burdy
 */
public class EditAction implements IObjectActionDelegate, IWorkbenchWindowActionDelegate {
	/** The current selection. */
	IStructuredSelection selection;
	/** the current active part */
	IWorkbenchPart activePart;

	public static void edit(ICompilationUnit cu) {
		IWorkbenchPart activePart = PlatformUI.getWorkbench()
				.getActiveWorkbenchWindow().getActivePage().getActivePart();
		IWorkbenchPartSite site = activePart.getSite();
		IWorkbenchPage page = site.getPage();
		try {
			PlatformUI.getWorkbench().showPerspective(
				JackPlugin.JACK_PERSPECTIVE_ID, page.getWorkbenchWindow());
		} catch (WorkbenchException e) {
			MessageDialog.openError(site.getShell(), JackPlugin.DIALOG_TITLE,
				"Error opening perspective: " + e.toString());
			return;
		}

		IViewPart view;

		try {
			view = page.showView(JackPlugin.CASE_EXPLORER_VIEW_ID);
		} catch (PartInitException e) {
			MessageDialog.openError(site.getShell(), JackPlugin.DIALOG_TITLE,
				"Error showing view: " + e.toString());
			return;
		}

		if (!SaveMessageDialog.saveModifiedRessources(activePart, "editing",
			JackPlugin.ALWAYS_SAVE_BEFORE_EDITING))
			return;

		if (cu != null) {
			SourceCaseViewer editor;
			CaseExplorer jv = (CaseExplorer) view;
			if (CompileMessageDialog.compileRessources(cu, activePart,
				"editing", JackPlugin.ALWAYS_COMPILE_BEFORE_EDITING, JackPlugin.JML_COMPILED)) {
				try {
					editor = (SourceCaseViewer) page
							.showView(JackPlugin.SOURCE_CASE_VIEWER_ID);

				} catch (PartInitException e) {
					MessageDialog.openError(site.getShell(),
						JackPlugin.DIALOG_TITLE, "Error showing view: "
								+ e.toString());
					return;
				}
				jv.setViewedFile(cu, editor);
			}
		}
	}

	public static void edit(IFile fi) {
		IWorkbenchPart activePart = PlatformUI.getWorkbench()
				.getActiveWorkbenchWindow().getActivePage().getActivePart();
		IWorkbenchPartSite site = activePart.getSite();
		IWorkbenchPage page = site.getPage();
		try {
			PlatformUI.getWorkbench().showPerspective(
				JackPlugin.JACK_PERSPECTIVE_ID, page.getWorkbenchWindow());
		} catch (WorkbenchException e) {
			MessageDialog.openError(site.getShell(), JackPlugin.DIALOG_TITLE,
				"Error opening perspective: " + e.toString());
			return;
		}

		IViewPart view;

		try {
			view = page.showView(JackPlugin.CASE_EXPLORER_VIEW_ID);
		} catch (PartInitException e) {
			MessageDialog.openError(site.getShell(), JackPlugin.DIALOG_TITLE,
				"Error showing view: " + e.toString());
			return;
		}

		if (!SaveMessageDialog.saveModifiedRessources(activePart, "editing",
			JackPlugin.ALWAYS_SAVE_BEFORE_EDITING))
			return;

		if (fi != null) {
			SourceCaseViewer editor;
			CaseExplorer jv = (CaseExplorer) view;
			try {
				editor = (SourceCaseViewer) page
						.showView(JackPlugin.SOURCE_CASE_VIEWER_ID);

			} catch (PartInitException e) {
				MessageDialog.openError(site.getShell(),
					JackPlugin.DIALOG_TITLE, "Error showing view: "
							+ e.toString());
				return;
			}
			jv.setViewedFile(new EditedFile(fi.getName(), fi.getProject()), editor);
		}
	}

	static MessageDialog getConfirmationMessageDialog(
			IWorkbenchPart activePart, String info, String question,
			String affirmation) {
		IWorkbenchPartSite site = activePart.getSite();
		String[] buttons = {"OK", "Cancel"};
		MessageDialog md = new MessageDialog(site.getShell(),
				JackPlugin.DIALOG_TITLE, null, info, MessageDialog.NONE,
				buttons, 0);
		return md;
	}

	ICompilationUnit getCompilationUnit() {
		if (selection.isEmpty()) {
			return null;
		}
		try {
			return (ICompilationUnit) selection.getFirstElement();
		} catch (ClassCastException e) {
			return null;
		}
	}

	private IFile getFile() {
		if (selection.isEmpty()) {
			return null;
		}
		try {
			return (IFile) selection.getFirstElement();
		} catch (ClassCastException e) {
			return null;
		}
	}

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		ICompilationUnit icu = getCompilationUnit();
		if (icu != null)
			edit(icu);
		else
			edit(getFile());
	}

	/**
	 * @see org.eclipse.ui.IObjectActionDelegate#setActivePart(IAction,
	 *      IWorkbenchPart)
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
			Object o;
			action.setEnabled((selection != null) &&
					((o = selection.getFirstElement()) instanceof ICompilationUnit)
					&& ((ICompilationUnit) o).getPath().toString().endsWith(".java"));
		}
//		} else { // can happen
//			// should never happen
//			MessageDialog.openError(activePart.getSite().getShell(),
//				"Jack Error",
//				"Unexpected selection type: expected StructuredSelection, "
//						+ "got " + sel.getClass().getName());
//		}

	}

	public void dispose() {	}

	public void init(IWorkbenchWindow window) { }

}