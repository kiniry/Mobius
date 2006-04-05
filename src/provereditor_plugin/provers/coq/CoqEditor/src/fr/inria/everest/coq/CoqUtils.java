package fr.inria.everest.coq;

import prover.ProverEditorPlugin;
import prover.exec.AProverException;
import fr.inria.everest.coq.coqtop.CoqTop;
import fr.inria.everest.coq.editor.CoqProverTranslator;

public class CoqUtils {
	public static CoqTop createNewCoqTop() throws AProverException {
		return (CoqTop) CoqProverTranslator.getInstance().createNewTopLevel(null);
	}
	public static CoqTop createNewCoqTop(String [] paths) throws AProverException {
		return (CoqTop) CoqProverTranslator.getInstance().createNewTopLevel(paths);
	}
	public static String getCoqTop() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getTop();
	}
	public static String getCoqIde() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getIde();
	}
}
