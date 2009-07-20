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
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PlatformUI;

//TODO message d'erreur en cas d'abscence de la clause decreases

/**
 * Action allowing openning the selection in the Jack PO viewer view.
 * @author L. Burdy
 */
public class AnnotationAction implements IObjectActionDelegate, IWorkbenchWindowActionDelegate {
	/** The current selection. */
	ICompilationUnit icu;


	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action) {
		IWorkbenchPart activePart = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getPartService().getActivePart();
		ProgressMonitorDialog pmd =
			new ProgressMonitorDialog(activePart.getSite().getShell());
		try {
			if(icu == null)
				return;
//			ICompilationUnit icu = (ICompilationUnit) selection.getFirstElement();
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
	 * @see org.eclipse.ui.IActionDelegate#selectionChanged(IAction, ISelection)
	 */
	public void selectionChanged(IAction action, ISelection sel) {
		if (sel instanceof IStructuredSelection) {
			IStructuredSelection selection = (IStructuredSelection) sel;
			Object o = selection.getFirstElement();
			if(o instanceof ICompilationUnit) {
				icu =  (ICompilationUnit) o;
		
				if(icu == null) {
					action.setEnabled(false);
					return;
				}
				else {
					//Logger.get().println(icu.toString());
					if(icu.getPath().toString().endsWith(".java")) {
						action.setEnabled(true);
					}
					else {
						action.setEnabled(false);
					}
				}
			}
			else {
				action.setEnabled(false);
			}
		} 

	}

	public void dispose() {	}

	public void init(IWorkbenchWindow window) {}



	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}

}