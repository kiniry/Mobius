package prover.exec.toplevel.exceptions;

import prover.Prover;

public class TimeOutException extends ToplevelException {
	/** A serial UID to have much more fun... */
	private static final long serialVersionUID = 1L;
	
	public TimeOutException(Prover pkind) {
		super(pkind, "Timed out !");
	}


}
