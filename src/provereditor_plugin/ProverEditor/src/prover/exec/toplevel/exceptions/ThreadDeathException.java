package prover.exec.toplevel.exceptions;

import prover.Prover;

public class ThreadDeathException  extends ToplevelException {

	public ThreadDeathException(Prover pkind) {
		super(pkind, "Unexpected thread death !");
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

}
