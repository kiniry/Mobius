///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: ProveFileAction.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package bPlugin;

import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

/**
 * Action allowing adding the selected file to the list of files that should 
 * be proved.
 * @author A. Requet
 */
public class ProveBAction extends ProveAction {

	/**
	 * Returns a ProofTask suitable for proving the given jpo file.
	 */
	protected ProofTask getProofTask(IFile jpo_file, ICompilationUnit c) {
		return new AtelierBProofTask(jpo_file, c);
	}
	public String toString() {
		return "with AtelierB";
	}

}
