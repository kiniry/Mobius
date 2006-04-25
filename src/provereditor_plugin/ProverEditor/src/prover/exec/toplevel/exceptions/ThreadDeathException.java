package prover.exec.toplevel.exceptions;

import prover.Prover;

/**
 * This exception is thrown if the thread associated with one
 * of the the stream was unexpectedly killed.
 */
public class ThreadDeathException  extends ToplevelException {
	/** A serial UID to have much more fun... */
	private static final long serialVersionUID = 1L;

	/**
	 * Create the exception.
	 * @param pkind the prover having one of its thread killed.
	 */
	public ThreadDeathException(Prover pkind) {
		super(pkind, "Unexpected thread death !");
	}
}
