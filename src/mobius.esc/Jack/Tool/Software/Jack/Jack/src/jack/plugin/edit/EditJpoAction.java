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
import jack.plugin.perspective.CaseExplorer;
import jack.plugin.perspective.SourceCaseViewer;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.WorkbenchException;

/**
 * Action allowing openning the selection in the Jack PO viewer view.
 * 
 * @author L. Burdy
 */
public class EditJpoAction extends EditAction {

	public static void edit(ICompilationUnit cu, String jpo) {
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
			jv.setViewedFile(new EditedFile(/*JackPlugin.getOutputDir(cu.getJavaProject().getProject()).getLocation().toFile().getAbsolutePath() + File.separatorChar +  */
					jpo + ".jpo",
					cu.getJavaProject().getProject()), 
					editor);
	}

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		IWorkbenchPart activePart = PlatformUI.getWorkbench()
		.getActiveWorkbenchWindow().getActivePage().getActivePart();
		IWorkbenchPartSite site = activePart.getSite();
		ICompilationUnit icu = getCompilationUnit();
		if (icu != null) {
			String jpo;
			try {
				jpo = icu.getResource().getPersistentProperty(JackPlugin.JPO_FROM_CLASS);
			}
			catch (CoreException ce) {
				MessageDialog.openError(site.getShell(), JackPlugin.DIALOG_TITLE,
										"Error opening jpo from annotated class file: " + ce.toString());
				return;
			}
			if (jpo ==null) {
				MessageDialog.openError(site.getShell(), JackPlugin.DIALOG_TITLE,
				"Class file has not been jml compiled.");
				return;
			}
			else
				edit(icu, jpo);
		}
	}


}