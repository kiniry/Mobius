package mobius.prover.coq.sugar;

import mobius.prover.ProverEditorPlugin;
import mobius.prover.exec.AProverException;

public class CoqUtils {
	public static CoqTop createNewCoqTop() throws AProverException {
		return createNewTopLevel(null);
	}
	
	public static String getCoqTop() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getTop();
	}
	public static String getCoqC() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getCompiler();
	}
	public static String [] getCommand(String [] path, String file) {
		return ProverEditorPlugin.getInstance().getProver("Coq").getTranslator().getCompilingCommand(getCoqC(), path, file);
	}
	public static String getCoqIde() {
		return ProverEditorPlugin.getInstance().getProver("Coq").getIde();
	}
	
	public static CoqTop createNewTopLevel(String[] path) throws AProverException {
		return new CoqTop(path);
	}
}
