/*
 * Created on Jun 29, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package coqPlugin.prooftask.action;

import jack.plugin.JackPlugin;
import jack.plugin.prove.ProofTask;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

import coqPlugin.prooftask.CoqToughProofTask;


public class ProveCoqToughAction extends AProveAction {
	protected ProofTask getProofTask(IFile jpo_file, ICompilationUnit c) {
		return new  CoqToughProofTask(JackPlugin.getBytecodeJpoFile(c),c);		
	}
	public String toString() {
		return "with Coq (tough)";
	}
}
