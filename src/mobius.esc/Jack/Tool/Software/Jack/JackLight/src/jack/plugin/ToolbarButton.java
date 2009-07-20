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

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
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


}
