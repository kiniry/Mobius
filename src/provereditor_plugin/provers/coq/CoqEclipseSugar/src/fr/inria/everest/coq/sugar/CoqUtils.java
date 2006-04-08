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
		return new CoqTop(path);
	}
}
