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
	 * The file extension for the history files.
	 */
	static public final String BYTECODE_HISTORY_EXTENSION   = ".bt";
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
	public static String replaceLast(String string, String oldSuffix, 
			                         String newSuffix) {
		if (string.endsWith(oldSuffix)) {
			// Return string with new suffix
			return string.substring(0, string.lastIndexOf(oldSuffix)).
			                                  concat(newSuffix);
		} else {
			// Given suffix does not occur
			return string;
		}
	}
	
	/**
	 * This is a convenience method to obtain the classpath
	 * separator relevant to the current operating system. 
	 *  
	 * @return the string that separates the classpath entries 
	 */
	public static String getClassPathSeparator() {
		return System.getProperty("path.separator");
	}

	/**
	 * This is a convenience method to obtain the separator 
	 * that separates subsequent direcotry and file entries
	 * in a path to a resource. This value is relevant to the current 
	 * operating system. 
	 *  
	 * @return the string that separates the file path entries 
	 */
	public static String getFileSeparator() {
		return System.getProperty("file.separator");
	}
	
	/**
	 * This method strips off all the whitespace characters
	 * in the given string
	 * 
	 * @param the string to strip the whitespace from
	 * @result the string with the whitespace stripped off
	 */
	public static String stripAllWhitespace(String l) {
		String s;
		s = "";
		int ii = 0;
		int jj = l.length();
		for (ii = 0; ii < jj; ii++)
			if (!(Character.isWhitespace(l.charAt(ii)))) {
				s += l.charAt(ii);
			}
		return s;	
	}
}