package annot.io;

/**
 * This exception occures when an attribute cannot be read correctly from BCEL's
 * Unknown attribute. That mean, BML annotations in .class file that is being
 * read are invalid or not supported by this library and this library cannot
 * continue reading following expressions or attributes (becouse of unknown
 * length of unsupported annotation).
 * 
 * @author tomekb
 */
public class ReadAttributeException extends Exception {

	private static final long serialVersionUID = 1L;

	/**
	 * A standard constructor, with single string messages describing error
	 * details.
	 * 
	 * @param msg -
	 *            short error description.
	 */
	public ReadAttributeException(String msg) {
		super(msg);
	}

}
