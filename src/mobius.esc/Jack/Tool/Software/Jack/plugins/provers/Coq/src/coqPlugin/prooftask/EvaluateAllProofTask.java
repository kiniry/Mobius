package coqPlugin.prooftask;

import java.io.File;

import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;
import jack.util.Logger;
import jpov.structure.Goal;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

import prover.exec.AProverException;

import coqPlugin.CoqFile;
import coqPlugin.prooftask.action.EvaluateAllAction;


public class EvaluateAllProofTask extends AProofTask {
	private String [][] tac = new String[1][1]; 
	public EvaluateAllProofTask(IFile jpo_file, ICompilationUnit c) {
		super(jpo_file, c);
	}

	public EvaluateAllProofTask() {
		super();
	}

	public ProofTask factory(IFile jpo_file, ICompilationUnit c) {
		return new EvaluateAllProofTask(jpo_file, c);
	}

	public boolean getCoqMustProveAll() {
		return false;
	}

	public String[][] getTactics() {
		return tac;
	}

	public String getProverName() {
		return "Coq: re-evaluate proofs";
	}

	public ProveAction factory() {
		return new EvaluateAllAction();
	}
	
	protected boolean proveLemma(String name, Goal g) 
		throws AProverException {
		
		String filename = CoqFile.getNameFromGoal(g);
		File f = new File(getJpoDir()+ File.separator +"proofs" + File.separator + filename);
		if(f.exists()) {
			CoqFile c = new CoqFile(f);
			tac[0][0] = c.getProof();
			Logger.get().println(f +" " + tac[0][0]);
			return super.proveLemma(name,g);
		}
		return false;
	}

}
