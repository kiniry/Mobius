/*
 * Created on Mar 7, 2005
 *
 */
package prover.plugins.exceptions;


/**
 * An exception when encountering incomplete proofs.
 * It is to express the fact that the proof the user is 
 * trying to save (or trying to do anything with it...)
 * is still incomplete.
 */
public class IncompleteProofException extends ProverException {

	/** A serial UID to have much more fun... */
	private static final long serialVersionUID = 1L;

	/**
	 * Create a new exception, with a message specifying the 
	 * problem.
	 * @param description A description of the problem encountered
	 */
	public IncompleteProofException(String description) {
		super(description);
	}

}
