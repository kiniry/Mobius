package prover.exec.toplevel.exceptions;

import prover.Prover;
import prover.exec.exceptions.ToplevelException;

public class ThreadDeathException  extends ToplevelException {

	public ThreadDeathException(Prover pkind) {
		super(pkind, "Unexpected thread death !");
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

}
