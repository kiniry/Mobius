//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package annotation;

import jack.plugin.JackJml2bConfiguration;
import jack.plugin.JackPlugin;

import java.lang.reflect.InvocationTargetException;

import jml2b.structure.java.JavaLoader;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

//TODO message d'erreur en cas d'abscence de la clause decreases

/**
 * Action allowing openning the selection in the Jack PO viewer view.
 * @author L. Burdy
 */
public class AnnotationAction implements IObjectActionDelegate {
	/** The current selection. */
	IStructuredSelection selection;
	/** the current active part */
	IWorkbenchPart activePart;

	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		ProgressMonitorDialog pmd =
			new ProgressMonitorDialog(activePart.getSite().getShell());
		try {
			ICompilationUnit icu = (ICompilationUnit) selection.getFirstElement();
			AnnotationGenerator ag = new AnnotationGenerator(
															 new JackJml2bConfiguration(icu.getJavaProject(), new JavaLoader()),
															 icu);
			pmd.run(
					false,
					false,
					ag);
			if (ag.getCreatedClass() != null)
			icu.getResource().setPersistentProperty(JackPlugin.ANNOTATED_CLASS, ag.getCreatedClass());
		} catch (CoreException ie) {
		} catch (InterruptedException ie) {
		} catch (InvocationTargetException ie) {
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