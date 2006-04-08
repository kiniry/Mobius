package prover.exec.toplevel.exceptions.toplevel;

import prover.Prover;
import prover.exec.toplevel.exceptions.ToplevelException;

public class TopLevelDeathException extends ToplevelException {

	public TopLevelDeathException(Prover pkind) {
		super(pkind, "Oh no ! TopLevel was killed !");
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

}
