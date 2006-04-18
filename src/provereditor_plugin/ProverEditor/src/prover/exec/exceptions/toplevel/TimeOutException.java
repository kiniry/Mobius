package prover.exec.exceptions.toplevel;

import prover.Prover;
import prover.exec.exceptions.ToplevelException;

public class TimeOutException extends ToplevelException {

	public TimeOutException(Prover pkind) {
		super(pkind, "Timed out !");
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

}
