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
	 * The file extension for the Java files.
	 */
	static public final String JAVA_EXTENSION       = ".java";
	/**
	 * The file extension for the Java class files.
	 */
	static public final String CLASS_EXTENSION      = ".class";
	/**
	 * The file extension for the files with the bytecode representation.
	 */
	static public final String BYTECODE_EXTENSION   = ".btc";
	/**
	 * The extension for BoogiePL files.
	 */	
	static public final String BOOGIEPL_EXTENSION = ".bpl";

	
	/**
	 * This method replaces the last occurrence of the <code>oldSuffix</code>
	 * with the <code>newSuffix</code> in <code>string</code>. It serves to 
	 * exchange the file sufficies. In case <code>oldSuffix</code> does not
	 * occur in <code>string</code> it returns <code>string</code>.
	 * 
	 * @param string string to replace the suffix from
	 * @param oldSuffix the suffix to replace
	 * @param newSuffix the new suffix
	 * @return the string with replaced suffix
	 */
	public static String replaceLast(String string, String oldSuffix, String newSuffix) {
		if (string.endsWith(oldSuffix)) {
			// Return string with new suffix
			return string.substring(0, string.lastIndexOf(oldSuffix)).concat(newSuffix);
		} else {
			// Given suffix does not occur
			return string;
		}
	}
}