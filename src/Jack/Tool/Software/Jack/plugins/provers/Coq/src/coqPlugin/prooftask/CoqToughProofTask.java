/*
 * Created on Mar 4, 2005
 *
 */
package coqPlugin.prooftask;

import jack.plugin.perspective.ICaseExplorer;
import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

import coqPlugin.PreferencePage;
import coqPlugin.prooftask.action.AProveAction;

/**
 * @author jcharles
 *
 */
public class CoqToughProofTask extends AProofTask{
	/**
	 * The tactics to use.
	 */
	private String [][] toughTactics = {{"toughAutoJack."}};
	
	
	/**
	 * A simple constructor.
	 */
	public CoqToughProofTask() {
		super();
	}
	/**
	 * @param jpo_file
	 * @param c
	 */
	public CoqToughProofTask(IFile jpo_file, ICompilationUnit c) {
		super(jpo_file, c);
	}
	/**
	 * @param c
	 */
	public CoqToughProofTask(ICaseExplorer c) {
		
		super(c);
	}
	public String getProverName() {
		return "Coq (Tough)";
	}
	
	public ProofTask factory(IFile jpo_file, ICompilationUnit c) {
		return new CoqToughProofTask(jpo_file, c);
	}

	/* (non-Javadoc)
	 * @see coqPlugin.CoqProofTask#getTactics()
	 */
	public String[][] getTactics() {
		return toughTactics;
	}
	/* (non-Javadoc)
	 * @see coqPlugin.CoqProofTask#getCoqMustProveAll()
	 */
	public boolean getCoqMustProveAll() {
		return PreferencePage.getCoqMustProveAllTough();
	}
	/* (non-Javadoc)
	 * @see jack.plugin.prove.ProofTask#factory(jack.plugin.perspective.ICaseExplorer)
	 */
	public ProveAction factory() {
		return new AProveAction();
	}


}
