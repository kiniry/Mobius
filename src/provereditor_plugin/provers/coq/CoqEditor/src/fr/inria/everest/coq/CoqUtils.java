package fr.inria.everest.coq;

import prover.ProverEditorPlugin;
import prover.exec.toplevel.exceptions.CoqException;
import fr.inria.everest.coq.coqtop.CoqTop;

public class CoqUtils {
	public static CoqTop createNewCoqTop() throws CoqException {
		return new CoqTop(getCoqTop(), null);
	}
	public static CoqTop createNewCoqTop(String [] paths) throws CoqException {
		return new CoqTop(getCoqTop(), paths);
	}
	public static String getCoqTop() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getTop();
	}
	public static String getCoqIde() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getIde();
	}
}
