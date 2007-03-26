package mobius.directVCGen.formula;

/**
 * The exception class to use with formulas. 
 * Every exception used in the visitors must be a subclass of this class.
 * @author J. Charles
 */
public class FormulaException extends Exception{
	/** */
	private static final long serialVersionUID = 1L;
	
	/**
	 * The simple constructor
	 */
	public FormulaException() {
	}
	
	/**
	 * The constructor with a message.
	 * @param string The debugging message of the exception
	 */
	public FormulaException(String string) {
		super(string);
	}
}
