package mobius.directVCGen.formula.type;

import mobius.directVCGen.formula.FormulaException;

/**
 * Exception from this class are made to describe type errors.
 * @author J. Charles
 */
public class TypeErrorException extends FormulaException {
	/** */
	private static final long serialVersionUID = 1L;
	
	/**
	 * The simple constructor
	 */
	public TypeErrorException() {
		super();
	}
	
	/**
	 * The constructor with a message.
	 * @param string The debugging message of the exception
	 */
	public TypeErrorException(String string) {
		super(string);
	}

}
