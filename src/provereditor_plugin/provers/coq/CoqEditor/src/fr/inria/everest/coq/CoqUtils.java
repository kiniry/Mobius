package fr.inria.everest.coq;

import prover.ProverEditorPlugin;
import prover.exec.toplevel.exceptions.ProverException;
import fr.inria.everest.coq.coqtop.CoqTop;

public class CoqUtils {
	public static CoqTop createNewCoqTop() throws ProverException {
		return new CoqTop(getCoqTop(), null);
	}
	public static CoqTop createNewCoqTop(String [] paths) throws ProverException {
		return new CoqTop(getCoqTop(), paths);
	}
	public static String getCoqTop() {
		return ProverEditorPlugin.getInstance().getProver("TopLevel").getTop();
	}
	public static String getCoqIde() {
		return ProverEditorPlugin.getInstance().getProver("TopLevel").getIde();
	}
}
