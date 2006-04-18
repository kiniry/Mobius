package prover.exec.exceptions.toplevel;

import prover.Prover;
import prover.exec.exceptions.ToplevelException;

public class TopLevelDeathException extends ToplevelException {

	public TopLevelDeathException(Prover pkind) {
		super(pkind, "Oh no ! TopLevel was killed !");
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

}
