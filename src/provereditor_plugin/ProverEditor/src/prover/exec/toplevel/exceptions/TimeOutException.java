package prover.exec.toplevel.exceptions;

import prover.Prover;

public class TimeOutException extends ToplevelException {

	public TimeOutException(Prover pkind) {
		super(pkind, "Timed out !");
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

}
