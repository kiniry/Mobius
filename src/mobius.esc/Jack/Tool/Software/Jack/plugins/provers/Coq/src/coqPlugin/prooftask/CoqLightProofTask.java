/*
 * Created on Mar 4, 2005
 *
 */
package coqPlugin.prooftask;

import jack.plugin.prove.ProofTask;
import jack.plugin.prove.ProveAction;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;

import coqPlugin.PreferencePage;
import coqPlugin.prooftask.action.ProveCoqLightAction;
import coqPlugin.prooftask.util.CoqDialog;


/**
 * @author jcharles
 *
 */
public class CoqLightProofTask extends AProofTask {
	private String [][] lightTactics = {{"lightAutoJack."}};
	private String [][] tactics = lightTactics;
	/**
	 * @param b
	 */
	public CoqLightProofTask() {
		super();
		tactics = this.lightTactics;
	}
	/**
	 * @param jpo_file
	 * @param c
	 */
	public CoqLightProofTask(IFile jpo_file, ICompilationUnit c) {
		super(jpo_file, c);
	}

	
	public String getProverName() {
		return "Coq (Light)";
	}
	public ProofTask factory(IFile jpo_file, ICompilationUnit c) {
		return new CoqLightProofTask(jpo_file, c);
	}
	/* (non-Javadoc)
	 * @see coqPlugin.CoqProofTask#getCoqMustProveAll()
	 */
	public boolean getCoqMustProveAll() {
		return PreferencePage.getCoqMustProveAllLight();
	}
	/* (non-Javadoc)
	 * @see coqPlugin.CoqProofTask#getTactics()
	 */
	public String[][] getTactics() {
		return tactics;
	}
	/* (non-Javadoc)
	 * @see jack.plugin.prove.ProofTask#factory(jack.plugin.perspective.ICaseExplorer)
	 */
	public ProveAction factory() {
		return new ProveCoqLightAction();
	}
	
	public void setPartial(String repos) {
		CoqDialog c = new CoqDialog(repos);
		int res = c.open();
		if (res == CoqDialog.OK) {
			tactics = new   String [1][];
			tactics[0] = new String [1];
			tactics [0][0]= c.getSelection();
		}
		else
			tactics = this.lightTactics;
	}
	public String toString() {
		return "with Coq (light)";
	}
	
}
