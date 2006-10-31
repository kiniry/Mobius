/**
 * TODO licence
 */
package javafe.extensions;

import javafe.util.UsageError;

/**
 * This interface provides access to all the extensions
 * that have to enhance the initialisation procedure,
 * in particular:
 * <ul>
 * <li> command line options
 * </ul>
 * 
 * @author Aleksy Schubert
 *
 */
public interface IJavafeInitComponentView {

	/**
	 * Process next tool option that belongs to the extension.
	 *
	 * <p> This routine handles the command-line options, storing the
	 * resulting information in the preceding instance variables and
	 * <code>Info.on</code>.
	 *
	 * @param option the option currently being handled.  An option
	 * always starts with a '-' character, and the remaining
	 * command-line arguments (not counting <code>option</code>)
	 * (<code>args[offset]</code>,...,<code>args[args.length-1]</code>).
	 * @param args the command-line arguments that are being processed.
	 * @param offset the offset into the <code>args</args> array that
	 * indicates which option is currently being dealt with.
	 * @return The offset to any remaining command-line arguments
     * should be returned or -1 in case no option from the extensions
     * is recognized.  (This allows the option to consume some or
     * all of the following arguments and to signal that no option
     * was recognized.)
	 * @exception UsageError If the option is erroneous, throw an
	 * {@link UsageError} exception with a string describing the
	 * problem.
	 */
	//@ requires option != null;
	//@ requires \nonnullelements(args);
	//@ requires 0 <= offset && offset <= args.length;
	//@ ensures (0 <= \result && \result <= args.length) || \result==-1;
	public int processOption(String option, String[] args, int offset) 
	               throws UsageError;

	/**
	 * This method generates a string which represents public
	 * options supplied by the current extension component. If the
	 * extension does not provide any public options the empty string
	 * "" is returned.
	 * 
	 * @return the string with options
	 */
	public /*@ non_null @*/ String showPublicOptions();

	/**
	 * This method generates a string which represents private
	 * options supplied by the current extension component. If the
	 * extension does not provide any private options the empty string
	 * "" is returned. The string should start with the banner:
	 * "The additional options from <Componen Name>"
	 * 
	 * @return the string with options
	 */	
	public /*@ non_null @*/ String showPrivateOptions();
	
	
	
}
