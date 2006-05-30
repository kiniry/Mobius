//******************************************************************************
/* Copyright (c) 2003, 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------

/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package coqPlugin.prooftask.action;

import jack.plugin.prove.ProofTask;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

import coqPlugin.prooftask.CoqLightProofTask;

/**
 * ProveFileAction that creates a ProofTask that uses the Simplify prover
 * for performing the proof.
 * @author A. Requet
 */
public class ProveCoqLightAction extends AProveAction {
	
	protected ProofTask getProofTask(IFile jpo_file, ICompilationUnit c) {
		return new CoqLightProofTask(jpo_file, c);
	}
	public String toString() {
		return "with Coq (light)";
	}


}
