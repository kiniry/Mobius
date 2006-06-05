//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ProveButton.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package bPlugin;

import jack.plugin.ToolbarButton;

import org.eclipse.jface.action.IAction;

/**
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 * @author A. Requet
 */
public class ProveBButton extends ToolbarButton {

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		runProofTask(action, new AtelierBProofTask());
//		
//		IWorkbenchPage page = getWindow().getActivePage();
//		Shell shell = getWindow().getShell();
//
//		IViewPart view;
//
//		try {
//			getWindow().getActivePage().showView(JavaUI.ID_PACKAGES);
//		} catch (PartInitException e) {
//			MessageDialog.openError(
//				shell,
//				JackPlugin.DIALOG_TITLE,
//				"Error showing view: " + e.toString());
//			return;
//		}
//
//		Iterator it = getSelection().iterator();
//
//		try {
//			// Warning: showing the page modifies the selection.
//			// So, the selection must be stored before calling page.showView
//			view = page.showView(JackPlugin.JACK_PROOF_VIEW_ID);
//		} catch (PartInitException e) {
//			MessageDialog.openError(
//				shell,
//				JackPlugin.DIALOG_TITLE,
//				"Error showing view: " + e.toString());
//			return;
//		}
//		ProofView proof_view = (ProofView) view;
//
//		List errors = null;
//		proof_view.freezeNotify();
//
//		while (it.hasNext()) {
//
//			ICompilationUnit c = (ICompilationUnit) it.next();
//			if (JackPlugin.isLock(c.getResource())) {
//				continue;
//			}
//			IFile java_file = (IFile) c.getResource();
//			IFile jpo_file = JackPlugin.getJpoFile(c);
//
//			if (jpo_file != null) {
//				JackPlugin.lock(c.getResource());
//				proof_view.addProof(new AtelierBProofTask(jpo_file, c));
//			} else {
//				if (errors == null) {
//					// creates the error vector if needed
//					errors = new Vector();
//				}
//				// adds the file name
//				errors.add(java_file.getName());
//			}
//		}
//
//		proof_view.unfreezeNotify();
//
//		if (errors != null) {
//			// errors have been encountered
//			String message =
//				"The following should be compiled before trying to prove them:";
//			// adds the list of files
//			Iterator files = errors.iterator();
//			while (files.hasNext()) {
//				message += "\n" + (String) files.next();
//			}
//
//			MessageDialog.openInformation(
//				shell,
//				JackPlugin.DIALOG_TITLE,
//				message);
//		}
	}


}
