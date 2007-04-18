/**
 * 
 */
package umbra;

/**
 * This is just container for common operations used in the
 * application.
 * 
 * @author alx
 *
 */
public class UmbraHelper {

	/**
	 * The file extension for the files with the bytecode representation.
	 */
	static public final String BYTECODE_EXTENSION   = ".btc";
	/**
	 * The file extension for the Java files.
	 */
	static public final String JAVA_EXTENSION       = ".java";
	/**
	 * The file extension for the Java class files.
	 */
	static public final String CLASS_EXTENSION      = ".class";
	/**
	 * The extension for BoogiePL files.
	 */	
	static public final String BOOGIEPL_EXTENSION = ".bpl";

	
	/**
	 * This method replaces the last occurrence of the <code>string2</code>
	 * with the <code>string3</code> in <code>string</code>. It serves to 
	 * exchange the file sufficies. In case <code>string2</code> does not
	 * occur in <code>string</code> it returns <code>string</code>.
	 * 
	 * @param string string to replace the suffix from
	 * @param string2 the suffix to replace
	 * @param string3 the new suffix
	 * @return the string with replaced suffix
	 */
	public static String replaceLast(String string, 
			                          String string2, String string3) {

		int where = string.lastIndexOf(string2);
		if (where==-1) { //does not occur
			return string;
		} else {
			return string.substring(0,where).concat(string3);
		}
	}
	
}
