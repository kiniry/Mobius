/**
 * 
 */
package javafe.extensions;

/**
 * This interface provides access to all the extensions
 * that have to enhance the lexing of ESC.
 * Particular extensions considered:
 * <ul>
 * <li> tag constants
 * </ul>
 * 
 * @author Aleksy Schubert
 *
 */
public interface IJavafeLexerComponentView {
	
	/**
	 * This method reserves a section of natural numbers
	 * that are needed to represent the lexer tags which are used
	 * by the component. It returns its argument when the
	 * component does not reserve any tags.
	 * 
	 * @param firstFree the first tag that is not assigned to 
	 *                  earlier tag constants
	 * @return the first free tag after all the tags in the component
	 */
	/*@ requires 
	  @      firstFree>=0;
	  @ ensures
	  @      firstFree>=\old(firstFree);
	  @*/
	public int reserveTagConstants(int firstFree);
			
	/**
     * If the given tag is implemented in the current component
     * then this method gives its string representation. When
     * the tag is not implemented here then <code>null</code>
     * is returned. 
     * 
	 * @param tag numeric identifier of the tag string to be returned
	 * @return the textual representation of the given tag or 
	 *         <code>null</code> when the tag is not implemented by
	 *         the current component. 
	 */
	/*@ requires
	  @       tag>=0;
	  @*/
	public String toString(int tag);

}
