/*
 * Created on Mar 3, 2005
 */
package prover.exec.exceptions;

import prover.Prover;


/**
 * @author jcharles
 *
 */
public class ToplevelException extends ProverException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;


	public ToplevelException(Prover pkind, String description) {
		super(pkind.getName() +".TopLevel", description);
	}

}
