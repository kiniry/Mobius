package fr.inria.everest.coq.sugar;

import prover.ProverEditorPlugin;
import prover.exec.AProverException;

public class CoqUtils {
	public static CoqTop createNewCoqTop() throws AProverException {
		return createNewTopLevel(null);
	}
	
	public static String getCoqTop() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getTop();
	}
	public static String getCoqIde() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getIde();
	}
	
	public static CoqTop createNewTopLevel(String[] path) throws AProverException {
		String [] cmds;
		if(path != null) {
			cmds = new String[2 + path.length * 2];
			for(int i = 0; i < path.length; i++) {
				cmds[(2 * i) + 1] = "-I";
				cmds[(2 * i) + 2] = path[i];
			}
			
		}
		else {
			cmds = new String[2];
		}
		cmds[0] = ProverEditorPlugin.getInstance().getProver("Coq").getTop();
		cmds[cmds.length - 1] = "-emacs";
		return new CoqTop(cmds, 10);
	}
}
