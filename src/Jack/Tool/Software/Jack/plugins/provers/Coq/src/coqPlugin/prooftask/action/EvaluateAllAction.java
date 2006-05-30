package coqPlugin.prooftask.action;

import jack.plugin.prove.ProofTask;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

import coqPlugin.prooftask.EvaluateAllProofTask;


public class EvaluateAllAction extends AProveAction {
	
	protected ProofTask getProofTask(IFile jpo_file, ICompilationUnit c) {
		return new EvaluateAllProofTask(jpo_file, c);
	}
	public String toString() {
		return "re-evaluate Coq proofs";
	}


}