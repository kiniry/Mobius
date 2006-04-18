package prover.exec.toplevel.exceptions;

import prover.Prover;

public class TopLevelDeathException extends ToplevelException {

	public TopLevelDeathException(Prover pkind) {
		super(pkind, "Oh no ! TopLevel was killed !");
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

}
