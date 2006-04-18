/*
 * Created on Mar 7, 2005
 *
 */
package prover.plugins.exceptions;


/**
 * An exception 
 * @author J. Charles
 */
public class IncompleteProofException extends ProverException {

	/** A serial UID to have much more fun... */
	private static final long serialVersionUID = 1L;

	/**
	 * @param description
	 */
	public IncompleteProofException(String description) {
		super(description);
	}

}
