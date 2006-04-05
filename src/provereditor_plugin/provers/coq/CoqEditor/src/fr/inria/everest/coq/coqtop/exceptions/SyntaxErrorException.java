/*
 * Created on Mar 7, 2005
 *
 */
package fr.inria.everest.coq.coqtop.exceptions;


/**
 * @author jcharles
 */
public class SyntaxErrorException extends CoqException{

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
