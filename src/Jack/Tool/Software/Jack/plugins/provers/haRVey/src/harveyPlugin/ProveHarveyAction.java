//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ProveSimplifyAction.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package harveyPlugin;
import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

/**
 * ProveFileAction that creates a ProofTask that uses the Simplify prover
 * for performing the proof.
 * @author A. Requet
 */
public class ProveHarveyAction extends ProveAction {
	
	protected ProofTask getProofTask(IFile jpo_file, ICompilationUnit c) {
		return new HarveyProofTask(jpo_file, c);
	}
}
