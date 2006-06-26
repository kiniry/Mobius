//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package bytecode_to_JPO;

import jack.util.Logger;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PlatformUI;

/**
 * Action allowing openning the selection in the Jack PO viewer view.
 * 
 * @author L. Burdy
 */
public class POGAction implements IObjectActionDelegate, IWorkbenchWindowActionDelegate {
	/** The current selection. */
	private Object selection;

	/*
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		ProgressMonitorDialog pmd = new ProgressMonitorDialog(
				PlatformUI.getWorkbench().getActiveWorkbenchWindow()
						.getPartService().getActivePart()
						.getSite().getShell());
		try {
			pmd.run(false, false, new POGGenerator(selection));
		} catch (InterruptedException ie) {
			Logger.err.println(ie);
		} catch (InvocationTargetException ie) {
			Logger.err.println(ie);
		}

	}

	/*
	 * @see org.eclipse.ui.IObjectActionDelegate#setActivePart(IAction,
	 *          IWorkbenchPart)
	 */
	public void setActivePart(IAction action, IWorkbenchPart targetPart) {}

	/*
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection sel) {
		if (sel instanceof IStructuredSelection) {
			IStructuredSelection iss = (IStructuredSelection) sel;
			selection = iss.getFirstElement();
			action.setEnabled((selection != null) &&
				(selection instanceof ICompilationUnit) && 
					((ICompilationUnit)selection).getPath().toString().endsWith(".java"));
		
		} 

	}

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchWindowActionDelegate#dispose()
	 */
	public void dispose() {}

	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchWindowActionDelegate#init(org.eclipse.ui.IWorkbenchWindow)
	 */
	public void init(IWorkbenchWindow window) {}

}