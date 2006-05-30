//******************************************************************************
/* Copyright (c) 2003, 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package coqPlugin.prooftask.action;

import jack.plugin.perspective.ICaseExplorer;
import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;

import coqPlugin.prooftask.CoqToughProofTask;

/**
 * ProveFileAction that creates a ProofTask that uses the Simplify prover
 * for performing the proof.
 * @author A. Requet
 */
public class AProveAction extends ProveAction {
	
	private static IProject proj = null;
	private static ICompilationUnit selection = null;
	protected ProofTask getProofTask(IFile jpo_file, ICompilationUnit c) {
		return new CoqToughProofTask(jpo_file, c);
	}
	
	protected ProofTask getProofTask(ICaseExplorer c) {
		return new CoqToughProofTask(c);
	}
	
	public void selectionChanged(IAction action, ISelection sel) {
		if (sel instanceof IStructuredSelection) {
			if(((IStructuredSelection) sel).getFirstElement() instanceof ICompilationUnit) {
				selection = (ICompilationUnit) ((IStructuredSelection) sel).getFirstElement();
				IProject p = selection.getResource().getProject();
				if (p != null)
					proj = p;
			}
		}
		super.selectionChanged(action, sel);
	}
	
	public static IProject getProject() {
		return proj;
	}
	public static ICompilationUnit getSelection() {
		return selection;
	}
}
