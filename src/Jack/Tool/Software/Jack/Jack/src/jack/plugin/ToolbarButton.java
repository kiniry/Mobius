//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ToolbarButton.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin;

import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProofView;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

/**
 * Base class for toolbar buttons.
 * <p>
 * This class adju
 * @author A. Requet, L. Burdy
 */
public abstract class ToolbarButton implements IWorkbenchWindowActionDelegate {

	private IStructuredSelection selection;
	private ICompilationUnit cmp_units = null;
	/**
	 * Returns the <code>IWorkbenchWindow</code> associated to this action.
	 */
	public IWorkbenchWindow getWindow() {
		return PlatformUI.getWorkbench().getActiveWorkbenchWindow();
	}

	/**
	 * Returns the current selection.
	 */
	public IStructuredSelection getSelection() {
		return selection;
	}

	public ICompilationUnit getCompilationUnits() {
		return cmp_units ;
	}
	
	/**
	 * Default implementation that does nothing.
	 * 
	 * @see org.eclipse.ui.IWorkbenchWindowActionDelegate#dispose()
	 */
	public void dispose() {
	}

	/**
	 * @see org.eclipse.ui.IWorkbenchWindowActionDelegate#init(IWorkbenchWindow)
	 */
	public void init(IWorkbenchWindow window) {
	}

	/**
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection selection) {
		if (selection instanceof IStructuredSelection) {
			this.selection = (IStructuredSelection) selection;
			if(!selection.isEmpty()) {
				Object o = this.selection.iterator().next();
				if(o instanceof ICompilationUnit)
					cmp_units = (ICompilationUnit)o;
			}
		} else {
			// error
			this.selection = null;
		}
	}

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void runProofTask(IAction action, ProofTask pt) {
		IWorkbenchPage page = getWindow().getActivePage();
		Shell shell = getWindow().getShell();

		IViewPart view;

		try {
			getWindow().getActivePage().showView(JavaUI.ID_PACKAGES);
		} catch (PartInitException e) {
			MessageDialog.openError(
				shell,
				JackPlugin.DIALOG_TITLE,
				"Error showing view: " + e.toString());
			return;
		}

		Iterator it = getSelection().iterator();

		try {
			// Warning: showing the page modifies the selection.
			// So, the selection must be stored before calling page.showView
			view = page.showView(JackPlugin.JACK_PROOF_VIEW_ID);
		} catch (PartInitException e) {
			MessageDialog.openError(
				shell,
				JackPlugin.DIALOG_TITLE,
				"Error showing view: " + e.toString());
			return;
		}
		ProofView proof_view = (ProofView) view;

		List errors = null;
		proof_view.freezeNotify();

		while (it.hasNext()) {

			ICompilationUnit c = (ICompilationUnit) it.next();
			if (JackPlugin.isLock(c.getResource())) {
				continue;
			}
			IFile java_file = (IFile) c.getResource();
			IFile jpo_file = JackPlugin.getJpoFile(c);

			if (jpo_file != null) {
				JackPlugin.lock(c.getResource());
				proof_view.addProof(pt.factory(jpo_file, c));
			} else {
				if (errors == null) {
					// creates the error vector if needed
					errors = new Vector();
				}
				// adds the file name
				errors.add(java_file.getName());
			}
		}

		proof_view.unfreezeNotify();

		if (errors != null) {
			// errors have been encountered
			String message =
				"The following should be compiled before trying to prove them:";
			// adds the list of files
			Iterator files = errors.iterator();
			while (files.hasNext()) {
				message += "\n" + (String) files.next();
			}

			MessageDialog.openInformation(
				shell,
				JackPlugin.DIALOG_TITLE,
				message);
		}
	}
	


}
