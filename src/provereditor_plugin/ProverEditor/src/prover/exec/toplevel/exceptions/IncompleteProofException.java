/*
 * Created on Mar 7, 2005
 *
 */
package prover.exec.toplevel.exceptions;


/**
 * @author jcharles
 *
 */
public class IncompleteProofException extends CoqException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param description
	 */
	public IncompleteProofException(String description) {
		super(description);
	}

}
