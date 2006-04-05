/*
 * Created on Mar 7, 2005
 *
 */
package prover.exec.toplevel.exceptions;


/**
 * @author jcharles
 */
public class SyntaxErrorException extends ProverException{

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param description
	 */
	public SyntaxErrorException(String description) {
		super(description);
	}

}
