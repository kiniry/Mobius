package prover.exec.toplevel.exceptions;

import prover.Prover;

public class ThreadDeathException  extends ToplevelException {
	/** A serial UID to have much more fun... */
	private static final long serialVersionUID = 1L;

	public ThreadDeathException(Prover pkind) {
		super(pkind, "Unexpected thread death !");
	}
}
