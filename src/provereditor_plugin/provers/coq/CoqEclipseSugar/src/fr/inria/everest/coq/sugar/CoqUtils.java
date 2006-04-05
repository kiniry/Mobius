package fr.inria.everest.coq.sugar;

import prover.ProverEditorPlugin;
import prover.exec.AProverException;
import fr.inria.everest.coq.editor.CoqProverTranslator;
import fr.inria.everest.coq.editor.BasicCoqTop;

public class CoqUtils {
	public static BasicCoqTop createNewCoqTop() throws AProverException {
		return (BasicCoqTop) CoqProverTranslator.getInstance().createNewTopLevel(null);
	}
	public static BasicCoqTop createNewCoqTop(String [] paths) throws AProverException {
		return (BasicCoqTop) CoqProverTranslator.getInstance().createNewTopLevel(paths);
	}
	public static String getCoqTop() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getTop();
	}
	public static String getCoqIde() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getIde();
	}
}
