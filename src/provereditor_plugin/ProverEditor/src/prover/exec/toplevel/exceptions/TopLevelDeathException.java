package prover.exec.toplevel.exceptions;

import prover.Prover;

public class TopLevelDeathException extends ToplevelException {
	/** A serial UID to have much more fun... */
	private static final long serialVersionUID = 1L;
	
	
	public TopLevelDeathException(Prover pkind) {
		super(pkind, "Oh no ! TopLevel was killed !");
	}


}
