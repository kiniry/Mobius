package annot.textio;

/**
 * This interface describe how BML annotations should be
 * displayed.
 * 
 * @author tomekb
 */
public interface IDisplayStyle {

	/**
	 * Debug mode (displays AST below each annotation).
	 */
	public static boolean goControlPrint = false;

	/**
	 * Maximum line width, for line-breaking.
	 */
	public static int max_total_line_width = 60;

	/**
	 * Wether display each implication branch of quantified
	 * formula at the same level as quantifier itself or not.
	 */
	public static final boolean go3argQuantifiers = true;

	/**
	 * Wether use simplified (raw) prettyPrinter or not.
	 * Set in to true only if main (advanced) prettyPrinter
	 * makes several errors and resulting code became
	 * unreadable.
	 */
	public static final boolean goUseSimplePrettyPrinter = false;

	/**
	 * Shows right margin in displayed code, after
	 * {@value #max_total_line_width}'s character,
	 * for prettyPrinter debugging only. Some features like
	 * CodeSearch mechanisms may not work with this flag on.
	 */
	public static final boolean goShowRightMargin = false;

	/**
	 * Beginning, next line, and end of BML annotation comment.
	 * All should have the same length:
	 */
	public static final String comment_start = "/* ";
	public static final String comment_next = " * ";
	public static final String comment_end = " */";

	/**
	 * length of comment marks above.
	 */
	public static final int comment_length = comment_next.length();

	/**
	 * block marks for an expression (beginning and end of
	 * expression block):
	 */
	public static final char expr_block_start = '{';
	public static final char expr_block_end = '}';

	/**
	 * Line indentation increament.
	 */
	public static final String lineIndent = "  ";

	/**
	 * JavaType display values:
	 */
	public static final String jt_int = "int";
	public static final String jt_boolean = "boolean";

	/**
	 * BML attribute names (stored in primary constantPool):
	 */
	public static final String __mspec = "method specification";
	public static final String __classInvariant = "class invariant";
	public static final String __assertTable = "assert table";
	public static final String __second_cp = "second constant pool";

	/**
	 * BML annotations keywords (at the beginning
	 * of annotations only).
	 */
	public static final String _classInvariant = "\\class invariant";
	public static final String _assert = "\\assert";
	public static final String _requires = "\\requires ";
	public static final String _sc_start = "{|";
	public static final String _sc_end = "|}";
	public static final String _precondition = "\\precondition";
	public static final String _postcondition = "\\ensures";

}
