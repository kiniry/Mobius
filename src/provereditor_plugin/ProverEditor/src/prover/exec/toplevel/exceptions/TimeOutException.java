package prover.exec.toplevel.exceptions;

import prover.Prover;

/**
 * This exception is thrown when the grace time has ended.
 * The prove is timed out.
 * @author J. Charles
 */
public class TimeOutException extends ToplevelException {
	/** A serial UID to have much more fun... */
	private static final long serialVersionUID = 1L;
	
	/**
	 * Create a new exception.
	 * @param pkind The prover being timed out
	 */
	public TimeOutException(Prover pkind) {
		super(pkind, "Timed out !");
	}
}
