/**
 * 
 */
package escjava.extensions;

import javafe.ast.Identifier;

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
public interface IESCLexerComponentView {
	
	/**
	 * This method reserves a section of natural numbers
	 * that are needed to represent the lexer tags which are used
	 * by the component. It returns its argument when the
	 * component does not reserve any tags.
	 * 
	 * @param firstFree the first tag that is not assigned to 
	 *                  earlier tag constants
	 * @return the first tag after all the tags in the component
	 *         have been reserved
	 */
	/*@ requires 
	  @      firstFree>=0;
	  @ ensures
	  @      firstFree>=\old(firstFree);
	  @*/
	public int reserveTagConstants(int firstFree);
	
	/**
	 * If the string parameter is a check identifier introduced
	 * by the current component then this method converts the string 
	 * to a corresponding token. Otherwise it returns -1.
	 * 
	 * @param s the string for which a token should be generated
	 * @return the value of the corresponding token or -1 when
	 *         the string does not correspond to any check token
	 *         introduced by the component
	 */
	/*@ 
	  @ ensures \result >= -1;
	  @*/
	public int checkFromString(/*@non_null*/ String s);
	
    /**
     * The method converts the given identifier object to the
     * corresponding integer tag value. If the keyword is not
     * introduced by the current component it returns -1.
     * 
     * @param keyword the keyword to lookup.
     * @return value of the tag corresponding to the keyword encoded 
     * as an {@link Identifier} in the parameter 'keyword'. 
     * A {@link #NULL} is returned if the identifier in question is 
     * not an ESC/Java or JML keyword known to {@link TagConstants}.
     */
	/*@ 
	  @ ensures \result >= -1;
	  @*/
	public int fromIdentifier(Identifier keyword);
	
	/**
	 * The method returns true when the given tag number
	 * is a keyword defined in the current component.
	 * Otherwise it returns false.
	 * 
	 * @param tag for which it is assessed if it is keyword
	 * @return true when the <code>tag</code> number is a keyword
	 *         defined in the current component
	 */
	/*@ requires
	  @       tag>=0;
	  @*/
	public boolean isKeywordTag(int tag);
	
	/**
	 * The method returns true when the given tag number
	 * represents a redundant identifier defined in the current 
	 * component. Otherwise it returns false.
	 * 
	 * @param tag for which it is assessed if it is redundant keyword
	 * @return true when the <code>tag</code> number is a redundant 
	 *         keyword defined in the current component
	 */
	/*@ requires
	  @       tag>=0;
	  @*/
	public boolean isRedundant(int tag);
	
	/**
	 * The method returns a redundant version of the given non-redundant
	 * tag for tags implemented in the current component. If the
	 * given tag has no redundant version or is not added by the
	 * current component then the tag itself is returned. 
	 * 
	 * @param tag is the tag number for which the redundant version
	 *        is searched
	 * @return the redundant version of the tag or the tag itself
	 *         when no redundant version is implemented by the
	 *         current component.
	 */
	/*@ requires
	  @       tag>=0;
	  @*/
	public int makeRedundant(int tag);
	
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
	
	/**
     * If the given tag is implemented in the current component
     * then this method gives its string representation appropriate
     * for VC generation. When the tag is not implemented here 
     * or there is no its VC version then <code>null</code> is returned. 
     * 
	 * @param tag numeric identifier of the tag string to be returned
	 * @return the textual representation of the given tag or 
	 *         <code>null</code> when the tag is not implemented by
	 *         the current component or when there is not VC version
	 *         of the tag
	 */
	/*@ requires
	  @       tag>=0;
	  @*/
	public String toVcString(int tag);
	
	/**
	 * The method returns a non-redundant version of the given redundant
	 * tag for tags implemented in the current component. If the
	 * given tag is not redundantor is not added by the
	 * current component then the tag itself is returned. 
	 * 
	 * @param tag is the tag number for which the non-redundant version
	 *        is searched
	 * @return the non-redundant version of the tag or the tag itself
	 *         when no redundant version is implemented by the
	 *         current component.
	 */
	/*@ requires
	  @       tag>=0;
	  @*/
	public int unRedundant(int tag);

}
